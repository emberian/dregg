/-
# Metatheory.Categorical — deriving the abstract spec from categorical first principles.

> The lead's aspiration: *"derive the abstract spec from categorical first principles and
> some really reasonable stuff."*

The `Dregg2.*` library and `Metatheory.ConstructiveKnowledge` **postulate** their spec
structures: `Dregg2.Core.Conservation` carries `tensor_add`/`unit_zero` as *fields* (the
monoid-hom is a hypothesis you assert when you build a `Conservation`); `Dregg2.Laws`
takes the `Predicate ⊣ Witness` Galois connection as a *named construction*; the cell
coalgebra `Dregg2.Boundary.TurnCoalg` is a *given* structure map. This module begins the
opposite movement: take a **minimal categorical axiom** and DERIVE the spec structure as
its *consequence*.

What is DERIVED-and-proved here (no `sorry`, kernel-clean, `#assert_axioms`-pinned):

* **§1 Conservation.** From the single categorical datum *"`Σ` is a lax monoidal functor
  `C ⥤ Discrete M`" (`M` a discrete `AddMonoid`)* we DERIVE — as the functor's *coherence
  morphisms*, not as assumed fields — `Σ̃(A ⊗ B) = Σ̃ A + Σ̃ B` (the tensorator `μ`) and
  `Σ̃ I = 0` (the unit `ε`). These are exactly the `tensor_add`/`unit_zero` that
  `Dregg2.Core.Conservation` postulates. We then DERIVE **no-free-copy** purely
  categorically: a comonoid copy map `Δ : A ⟶ A ⊗ A` that `Σ` respects forces
  `Σ̃ A = Σ̃ A + Σ̃ A`, hence `Σ̃ A = 0` in a cancellative `M`. The Lean-side shadow of this
  is `Dregg2.Core.withholding_no_free_copy`.

* **§2 The verify/find seam.** We frame `Predicate ⊣ Witness` as a genuine
  `GaloisConnection` (mathlib `Order.GaloisConnection`) and DERIVE the seam's
  closure/monotonicity facts — attenuation (right adjoint monotone), the demand/supply
  round-trips (unit/counit), and the closure idempotence — as standard *consequences* of
  the adjunction, not as separately-stated laws.

* **§3 (universal property stated).** The cell as a coalgebra of `F X = Obs × (Adm → X)`
  and the hyperedge/JointTurn binding as a (wide) **pullback** in the category of
  coalgebras — stated faithfully via mathlib `CategoryTheory.Limits`. The *anamorphism*
  (final-coalgebra existence) is honestly OPEN.

## The `study-category §5` honesty caveat (do not oversell "strong monoidal")

Functoriality into a **discrete** target is *thin*. In `Discrete M` every hom is a
proof-of-equality (`Discrete.eq_of_hom : (X ⟶ Y) → X.as = Y.as`), so the *only* content a
(lax/strong) monoidal functor to `Discrete M` carries is **the equations its coherence
morphisms witness** — `Σ̃(A⊗B) = Σ̃A + Σ̃B`, `Σ̃ I = 0`, and the invariance `Σ̃ A = Σ̃ B`
along any turn `A ⟶ B`. The associativity/unitality coherence *diagrams* are automatic
(every diagram in a discrete category commutes). So the honest reading of "conservation =
a monoidal functor" is **monoid-hom on counts + invariance on morphisms** (per
`Dregg2.Core` docstring / `dregg2.md §2.1`), and the "strong monoidal" packaging is
*decorative*. We DERIVE precisely the thin content and say so; we do not claim the rich
structure of a non-degenerate monoidal functor.

DISCIPLINE: faithful Props; honest `-- OPEN:` (precisely stated) on the one genuinely-open
obligation (the anamorphism). `#assert_axioms` pins the proved keystones.
-/
import Dregg2.Core
import Dregg2.Laws
import Dregg2.Tactics
import Dregg2.Finality
import Dregg2.Confluence
import Mathlib.CategoryTheory.Monoidal.Discrete
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Hom.Lattice

namespace Metatheory

open CategoryTheory MonoidalCategory

universe u v w

/-! # §1. Conservation, DERIVED from a lax monoidal functor to a discrete monoid.

`Dregg2.Core` *postulates* the conservation measure's two monoid-hom equations
(`Conservation.tensor_add`, `Conservation.unit_zero`) as **fields**. Here we DERIVE them
from a single categorical datum.

THE ONE CATEGORICAL AXIOM (a named hypothesis, "some really reasonable stuff"):

> Conservation is a **lax monoidal functor** `Σ : C ⥤ Discrete M` from the symmetric
> monoidal category `C` of cells/turns to the **discrete** monoidal category on a
> commutative `AddMonoid` `M`.

Everything in this section is a *consequence* of that single datum — extracted by reading
off the coherence morphisms `ε`/`μ` through `Discrete.eq_of_hom`. -/

section Conservation

open Functor.LaxMonoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {M : Type w} [AddCommMonoid M]

/-- The conservation measure **read off** a lax monoidal functor to the discrete monoid:
`Σ̃ A := (Σ.obj A).as`. This is the only data a functor-to-`Discrete M` carries at the
object level — the count assigned to a cell. -/
def measure (Sig : C ⥤ Discrete M) (A : C) : M := (Sig.obj A).as

/-- **DERIVED: the unit law `Σ̃ I = 0`** — *not assumed*. It is exactly the existence of
the lax-monoidal unit coherence morphism `ε Σ : 𝟙_(Discrete M) ⟶ Σ.obj (𝟙_ C)`: in a
discrete category a morphism IS an equality of objects (`Discrete.eq_of_hom`), and the
discrete-monoidal unit has `.as = 0`. This is `Dregg2.Core.Conservation.unit_zero`,
recovered as a theorem about the functor rather than a postulated field. -/
theorem measure_unit (Sig : C ⥤ Discrete M) [Sig.LaxMonoidal] :
    measure Sig (𝟙_ C) = 0 := by
  -- `ε Sig : 𝟙_ (Discrete M) ⟶ Sig.obj (𝟙_ C)` is a morphism in a discrete category…
  have h := Discrete.eq_of_hom (ε Sig)
  -- …so it forces `(𝟙_ (Discrete M)).as = (Sig.obj (𝟙_ C)).as`. The LHS is `0`.
  simpa [measure, Discrete.addMonoidal_tensorUnit_as] using h.symm

/-- **DERIVED: the additivity / monoid-hom law `Σ̃ (A ⊗ B) = Σ̃ A + Σ̃ B`** — *not
assumed*. It is exactly the existence of the lax-monoidal **tensorator**
`μ Σ A B : Σ.obj A ⊗ Σ.obj B ⟶ Σ.obj (A ⊗ B)`: by `Discrete.eq_of_hom` this morphism IS
the equation `(Σ.obj A ⊗ Σ.obj B).as = (Σ.obj (A ⊗ B)).as`, and in the discrete *additive*
monoidal category `(Σ.obj A ⊗ Σ.obj B).as = (Σ.obj A).as + (Σ.obj B).as`. This is
`Dregg2.Core.Conservation.tensor_add`, recovered as a consequence of the functor's
coherence rather than a postulated field. -/
theorem measure_tensor (Sig : C ⥤ Discrete M) [Sig.LaxMonoidal] (A B : C) :
    measure Sig (A ⊗ B) = measure Sig A + measure Sig B := by
  have h := Discrete.eq_of_hom (μ Sig A B)
  simpa [measure, Discrete.addMonoidal_tensorObj_as] using h.symm

set_option linter.unusedSectionVars false in
/-- **DERIVED: invariance along ordinary turns `Σ̃ A = Σ̃ B`** — *not assumed*. Any
morphism `f : A ⟶ B` in `C` (a turn) is sent by the functor to `Σ.map f : Σ.obj A ⟶
Σ.obj B`, a morphism in the discrete target, hence (`Discrete.eq_of_hom`) the equation
`Σ̃ A = Σ̃ B`. This is the content of `Dregg2.Core.conservation_ordinary` — that an honest
turn neither creates nor destroys resource — recovered as plain functoriality into a
discrete category. (The mint/burn generators are exactly the morphisms one must *remove*
from `C` for this to be the whole story: in the full system they live in a larger category
where `Σ` is only lax/oplax-invariant; here the discrete-target shadow makes EVERY
remaining morphism conservation-preserving.) Invariance needs neither `MonoidalCategory C`
nor `AddCommMonoid M` — it is bare functoriality into a discrete category — so the
unused-section-variable linter is locally silenced. -/
theorem measure_invariant (Sig : C ⥤ Discrete M) {A B : C} (f : A ⟶ B) :
    measure Sig A = measure Sig B :=
  Discrete.eq_of_hom (Sig.map f)

/-- **DERIVED: no-free-copy, categorically.** A **comonoid copy map** on `A` — any
morphism `copy : A ⟶ A ⊗ A` of the monoidal category (the comultiplication `Δ` a comonoid
object would carry; we take it as the bare morphism, which is all the argument needs) —
is sent by functoriality of `Σ` into the discrete target to a morphism
`Σ.obj A ⟶ Σ.obj (A ⊗ A)`, forcing (by invariance + additivity) `Σ̃ A = Σ̃ A + Σ̃ A`. In a
**cancellative** `M` (`IsCancelAdd`) that collapses to `Σ̃ A = 0`: there is NO
conservation-respecting duplication of a non-empty resource.

This is the substructural "no Δ" of conservation, DERIVED from
*(a comonoid copy morphism) + (lax monoidal functor to a cancellative discrete monoid)* — no
extra postulate. It is the categorical first-principles source of
`Dregg2.Core.withholding_no_free_copy` (whose hypotheses — `tensor_add`, the ordinary-turn
balance, cancellation — are exactly `measure_tensor`, `measure_invariant`, `IsCancelAdd`
here); there, the copy map appears as an *ordinary* `Turn A (A ⊗ A)`, the morphism analogue
of `copy` here.

(We use the bare copy morphism rather than mathlib's `ComonObj` typeclass *only* because
`Mathlib.CategoryTheory.Monoidal.Comon_` is not built in this lib's pinned mathlib slice;
the argument is identical — it consumes only `Σ.map copy`, i.e. that `copy` is *a* morphism
`A ⟶ A ⊗ A` — and a `ComonObj A` would supply exactly such a `copy := Δ[A]`.) -/
theorem no_free_copy [IsCancelAdd M]
    (Sig : C ⥤ Discrete M) [Sig.LaxMonoidal] (A : C) (copy : A ⟶ A ⊗ A) :
    measure Sig A = 0 := by
  -- the copy map, mapped through `Sig`, is invariant: `Σ̃ A = Σ̃ (A ⊗ A)`.
  have hinv : measure Sig A = measure Sig (A ⊗ A) := measure_invariant Sig copy
  -- additivity unfolds the target: `Σ̃ (A ⊗ A) = Σ̃ A + Σ̃ A`.
  rw [measure_tensor Sig A A] at hinv
  -- `Σ̃ A = Σ̃ A + Σ̃ A` ⟹ `Σ̃ A = 0` by left-cancellation.
  exact left_eq_add.mp hinv

/-! ### §1(a) deepened: conservation IS substructurality (the *absence of a natural Δ*).

`no_free_copy` shows a *single* copy morphism is conservation-trivial. The first-principles
statement is stronger and structural: conservation is exactly **the linear/affine
discipline — there is no natural diagonal `Δ`** that `Σ` respects on resource-bearing
objects. We make the linear and affine readings precise.

* **Linear (no copy = no Δ):** a *family* of copy maps `δ A : A ⟶ A ⊗ A`, natural or not,
  forces every count to `0`. So a cartesian (diagonal-bearing) structure is incompatible
  with non-trivial conservation: `C` carrying conservation **cannot** be cartesian on the
  resource fragment. This is "conservation = substructural / no-contraction."
* **Affine (no discard = no `!`):** dually, a *discard* `wk A : A ⟶ I` (the affine
  weakening `!`/projection to the unit) forces `Σ̃ A = 0` likewise (`Σ̃ A = Σ̃ I = 0`).
  Conservation tolerates neither contraction (`Δ`) nor, on counted objects, weakening
  (`wk`) — the **linear** reading, where resource is used *exactly* once. -/

set_option linter.unusedSectionVars false in
/-- **DERIVED (affine reading): no-free-discard.** A *discard / weakening* map
`wk : A ⟶ 𝟙_ C` (the affine `!`-projection to the monoidal unit) forces `Σ̃ A = 0`:
functoriality sends it to `Σ̃ A = Σ̃ I`, and `measure_unit` gives `Σ̃ I = 0`. So no counted
resource may be silently dropped — the *affine* half of substructurality. (Needs no
cancellativity: discarding is even more directly conservation-trivial than copying.) -/
theorem no_free_discard (Sig : C ⥤ Discrete M) [Sig.LaxMonoidal] (A : C)
    (wk : A ⟶ 𝟙_ C) : measure Sig A = 0 := by
  rw [measure_invariant Sig wk]; exact measure_unit Sig

/-- **DERIVED (linear reading): a *natural* diagonal collapses the whole measure.** If `C`
carries a diagonal `δ A : A ⟶ A ⊗ A` on *every* object (the data of a cartesian / Δ-bearing
structure — we ask only the components, naturality is not needed for the collapse), then a
conservation functor into a cancellative discrete monoid measures **everything** as `0`:
`∀ A, Σ̃ A = 0`. Contrapositive — the categorical first principle — *any non-trivial
conservation measure proves the absence of a global diagonal*: a Δ-bearing (cartesian)
monoidal category admits no faithful conservation. This is precisely "conservation = no
free copy = substructurality," now as a statement about the category's structure, not one
morphism. -/
theorem diagonal_collapses_measure [IsCancelAdd M]
    (Sig : C ⥤ Discrete M) [Sig.LaxMonoidal]
    (δ : ∀ A : C, A ⟶ A ⊗ A) : ∀ A : C, measure Sig A = 0 :=
  fun A => no_free_copy Sig A (δ A)

/-- **The linear-logic punchline (DERIVED, contrapositive):** a conservation functor with
*any* non-zero count witnesses that `C` has **no** global diagonal — `C` is genuinely
substructural (non-cartesian) on the resource fragment. The absence of a natural copy IS
conservation; their conjunction is contradictory once a single count is non-zero. -/
theorem nonzero_count_forbids_diagonal [IsCancelAdd M]
    (Sig : C ⥤ Discrete M) [Sig.LaxMonoidal]
    {A : C} (hA : measure Sig A ≠ 0) : ¬ ∃ δ : ∀ A : C, A ⟶ A ⊗ A, True :=
  fun ⟨δ, _⟩ => hA (diagonal_collapses_measure Sig δ A)

/-- **Bridge to the postulated spec.** Every lax monoidal functor `Σ : C ⥤ Discrete M`
*induces* the object-level monoid-hom data that `Dregg2.Core.Conservation` postulates as
fields: the `count = measure Σ`, with `unit_zero = measure_unit` and
`tensor_add = measure_tensor` now THEOREMS. We package the derived pair to make explicit
that the postulated fields are consequences. (The full `Conservation` structure additionally
carries the mint/burn *inflow/outflow* bookkeeping, which is candidate-operational data, not
categorical; we derive precisely the monoid-hom core it postulates.) -/
theorem conservation_core_derived (Sig : C ⥤ Discrete M) [Sig.LaxMonoidal] :
    (measure Sig (𝟙_ C) = 0) ∧
      (∀ A B : C, measure Sig (A ⊗ B) = measure Sig A + measure Sig B) :=
  ⟨measure_unit Sig, measure_tensor Sig⟩

end Conservation

/-! ### §1 honesty caveat, restated at the point of use (`study-category §5`).

`measure_unit`/`measure_tensor`/`measure_invariant` are the *entire* content of "`Σ` is a
monoidal functor to `Discrete M`": the associativity/unitality coherence **diagrams** of
the `LaxMonoidal` structure are vacuous here (every diagram in a discrete category
commutes, `Subsingleton (X ⟶ Y)`), so they impose nothing beyond these three equations.
Hence we have DERIVED *monoid-hom + invariance*, and ONLY that — the genuinely thin content
the `Dregg2.Core` docstring already flags. We do not claim, and the discrete target cannot
provide, the richer structure of a strong monoidal functor into a non-degenerate category. -/

/-! # §2. The verify/find seam, DERIVED as a Galois connection.

`Dregg2.Laws` constructs the `Predicate ⊣ Witness` Galois connection from a relation
(`polarity_galois`). Here we take *"the seam is a `GaloisConnection demand supply`"* as the
single categorical datum (an adjunction between the two preorders-as-thin-categories) and
DERIVE the seam's operational laws — attenuation, the demand/supply round-trips, closure
idempotence — as standard adjunction consequences. None of these is separately postulated;
each is `GaloisConnection.*` applied to the seam. -/

section Seam

variable {Demand : Type u} {Supply : Type v}
-- `Supply` is a `PartialOrder` (so the verification closure is genuinely idempotent — an
-- *equality*, via antisymmetry); `Demand` a `Preorder` suffices for the round-trips.
variable [Preorder Demand] [PartialOrder Supply]

/-- **The seam, as one categorical datum.** `verifies` (the right adjoint / "what a supply
verifies") and `realizes` (the left adjoint / "the demand a witness realizes") form a
`GaloisConnection` — equivalently an adjunction `realizes ⊣ verifies` between the
preorders-as-thin-categories `Supply` and `Demand`. This is the abstract `Predicate ⊣
Witness` of `Dregg2.Laws`, stated as the seam's defining property. -/
structure Seam where
  /-- Left adjoint: the (strongest) demand a supply realizes. -/
  realizes : Supply → Demand
  /-- Right adjoint: the (weakest) supply that verifies a demand. -/
  verifies : Demand → Supply
  /-- The adjunction: `realizes s ≤ d ↔ s ≤ verifies d` (demand⊣supply). -/
  adj : GaloisConnection realizes verifies

variable (S : Seam (Demand := Demand) (Supply := Supply))

/-- **DERIVED: attenuation is monotone (the right adjoint is monotone).** A weaker demand
is verified by a weaker supply: `verifies` is monotone. In the seam reading, *attenuating a
demand attenuates its required witness-strength* — the right-adjoint monotonicity that
`Dregg2.Laws`/`ConstructiveKnowledge §3` reads as the discipline of attenuation. Consequence
of the adjunction (`GaloisConnection.monotone_u`), not a separate law. -/
theorem seam_attenuate_monotone : Monotone S.verifies :=
  S.adj.monotone_u

/-- **DERIVED: `realizes` (demand-extraction) is monotone too** — `GaloisConnection.monotone_l`. -/
theorem seam_realizes_monotone : Monotone S.realizes :=
  S.adj.monotone_l

/-- **DERIVED: the supply round-trip (unit of the adjunction).** Verifying the demand a
supply realizes returns *no less* supply than you started with: `s ≤ verifies (realizes s)`.
This is the adjunction **unit** — "supply, demand-extracted then re-verified, is recovered
up to ≤" — `GaloisConnection.le_u_l`. The "demand⊣supply round-trip" of `§2`. -/
theorem seam_unit (s : Supply) : s ≤ S.verifies (S.realizes s) :=
  S.adj.le_u_l s

/-- **DERIVED: the demand round-trip (counit of the adjunction).** Extracting the demand of
the witness that verifies a demand returns *no more* demand: `realizes (verifies d) ≤ d`.
The adjunction **counit** — `GaloisConnection.l_u_le`. Together with `seam_unit` this is the
full unit/counit of `realizes ⊣ verifies`. -/
theorem seam_counit (d : Demand) : S.realizes (S.verifies d) ≤ d :=
  S.adj.l_u_le d

/-- **DERIVED: the verification closure is idempotent.** The composite
`verifies ∘ realizes` (verify the demand your supply realizes) is a **closure operator**:
applying it twice is applying it once. Idempotence is a standard adjunction consequence
(`GaloisConnection.u_l_u_eq_u` composed). In the seam reading: *re-verifying a
once-verified supply adds nothing* — the matcher reaches a fixed point in one round. -/
theorem seam_closure_idem (s : Supply) :
    S.verifies (S.realizes (S.verifies (S.realizes s)))
      = S.verifies (S.realizes s) :=
  -- `u (l (u b)) = u b` (`GaloisConnection.u_l_u_eq_u`) at `b := realizes s`.
  S.adj.u_l_u_eq_u (S.realizes s)

/-- **Bridge to `Dregg2.Laws`.** The concrete `Predicate ⊣ Witness` connection
`Dregg2.Laws.predicate_witness_galois` is exactly a `Seam` (its `realizes`/`verifies` are
the polar maps; `adj` is that connection). So §2's derived laws specialize to the verify/find
seam of the real system. We record the abstract round-trip that instantiates there. -/
theorem seam_roundtrip (s : Supply) (d : Demand)
    (h : S.realizes s ≤ d) : s ≤ S.verifies d :=
  (S.adj s d).mp h

end Seam

/-! # §4. Ordering / finality, DERIVED as a bounded lattice (the second judgement).

`Dregg2.Finality` *postulates* the four-tier ladder as a `LinearOrder Tier` with the
cross-tier commit rule `crossTierJoin := max` as a *named definition* and `no_downgrade`
as a separately-proved run-monotonicity. Here we take *"finality is a **bounded lattice**
of strengths, and commit = the **join** (least upper bound)"* as the single order-theoretic
datum. The mathlib **lattice laws then specialize to the Tier order**: the load-bearing
output of this section is that the *real* `Dregg2.Finality.Tier`'s `crossTierJoin` is the
lattice join (`tier_commit_eq_crossTierJoin`), so commit is monotone (`commit_monotone`) and
never-downgrades on the actual ladder (`tier_crossTierJoin_no_downgrade`).

The intermediate `commitAtMax_*_def` lemmas below (`a ≤ a ⊔ b`, `a ⊔ b ≤ ⊤`, `sup_assoc`,
`sup_comm`) are NOT derivations — they are mathlib's lattice/`BoundedOrder` facts restated at
the abstract `commitAtMax := ⊔`. They earn their place only as the bricks the two
`Tier`-touching results stand on; we name them `_def` and frame them as *unfolds of the join*,
not as postulate-free re-derivations of a finality rule.

THE ONE ORDER-THEORETIC AXIOM: *the finality tiers form a `Lattice τ` (a poset with binary
joins), and the cross-tier commit of a multi-tier turn is the **join** `a ⊔ b`.* (A
`BoundedOrder` additionally names a weakest `⊥` and a strongest `⊤` tier.) -/

section Finality

variable {τ : Type u} [Lattice τ]

/-- **Commit-at-max — the cross-tier commit rule, as the lattice join.** A turn touching
cells of tiers `a` and `b` commits at their **join** `a ⊔ b`: the *least* tier at least as
strong as both. This is `Dregg2.Finality.crossTierJoin` recovered as the lattice operation,
not a separate `max` definition. -/
def commitAtMax (a b : τ) : τ := a ⊔ b

/-- **`commitAtMax_le_left_def`** — `commitAtMax` UNFOLDS its left bound: `a ≤ a ⊔ b` is
mathlib's `le_sup_left`, restated at `commitAtMax`. Not a derivation of a finality rule — just
the join's upper-bound law. It is the brick the real-`Tier` `tier_crossTierJoin_no_downgrade`
("a commit never falls below either participant's tier") stands on. -/
theorem commitAtMax_le_left_def (a b : τ) : a ≤ commitAtMax a b := le_sup_left

/-- **`commitAtMax_le_right_def`** — the right companion (`b ≤ a ⊔ b`, `le_sup_right`). -/
theorem commitAtMax_le_right_def (a b : τ) : b ≤ commitAtMax a b := le_sup_right

/-- **`commit_monotone` (the load-bearing §4 law).** The cross-tier commit `(a,b) ↦ a ⊔ b` is
**monotone**: strengthening either participant's tier can only strengthen (never weaken) the
commit. The mathlib `sup_le_sup` specialized to the Tier order — this is the structural
content of "no-downgrade" (finality is an order-homomorphism), and it is one of the two
results this section actually exports to the real `Tier` (via `tier_commit_eq_crossTierJoin`). -/
theorem commit_monotone : Monotone (fun p : τ × τ => commitAtMax p.1 p.2) :=
  fun _ _ h => sup_le_sup h.1 h.2

/-- **`commitAtMax_assoc_def` / `commitAtMax_comm_def`** — `commitAtMax` UNFOLDS to the join's
`sup_assoc`/`sup_comm`, so an N-cell commit is well-defined independent of grouping/order.
These are mathlib lattice laws restated at `commitAtMax`, not postulate-free derivations. -/
theorem commitAtMax_assoc_def (a b c : τ) :
    commitAtMax (commitAtMax a b) c = commitAtMax a (commitAtMax b c) := sup_assoc a b c
theorem commitAtMax_comm_def (a b : τ) : commitAtMax a b = commitAtMax b a := sup_comm a b

/-- **`commitAtMax_le_top_def`** — the `BoundedOrder` law `a ⊔ b ≤ ⊤` restated at
`commitAtMax` (mathlib `le_top`): a commit cannot exceed the strongest tier. An unfold of the
join's top bound, not a derivation. -/
theorem commitAtMax_le_top_def [OrderTop τ] (a b : τ) : commitAtMax a b ≤ ⊤ := le_top

/-- **DERIVED (bounded): a weakest tier `⊥` is the commit-identity.** In a `BoundedOrder`
the bottom tier (the weakest mechanism — causal-only) is the join-identity: committing a
cell with a `⊥`-tier participant leaves its tier unchanged. -/
theorem commit_bot_identity [OrderBot τ] (a : τ) : commitAtMax ⊥ a = a := by
  simp [commitAtMax]

/-! ### §4 bridge: the abstract finality lattice IS `Dregg2.Finality.Tier`.

`Dregg2.Finality.Tier` is a `LinearOrder` (hence a `Lattice`), and its `crossTierJoin` is
exactly the lattice join. We additionally **derive the bounded structure** `Dregg2` leaves
implicit: the ladder has a weakest tier `⊥ = causal` and a strongest `⊤ = constitutional`,
so it is a genuine *bounded* lattice — the abstract §4 datum, realised. -/

open Dregg2.Finality in
/-- **The four-tier ladder has a strongest tier (DERIVED `OrderTop`).** `constitutional`
(rank 4) dominates every tier — the top of the §2.2 ladder. -/
instance tierOrderTop : OrderTop Dregg2.Finality.Tier where
  top := Dregg2.Finality.Tier.constitutional
  le_top t := by cases t <;> decide

open Dregg2.Finality in
/-- **The four-tier ladder has a weakest tier (DERIVED `OrderBot`).** `causal` (rank 1) is
below every tier — the coordination-free floor of the §2.2 ladder. -/
instance tierOrderBot : OrderBot Dregg2.Finality.Tier where
  bot := Dregg2.Finality.Tier.causal
  bot_le t := by cases t <;> decide

/-- **DERIVED: the tier ladder is a *bounded* lattice.** Combining the derived `OrderTop`
and `OrderBot`, `Tier` is a `BoundedOrder` — `causal ≤ t ≤ constitutional` for every `t`.
The abstract §4 "bounded lattice of finality strengths" is the concrete `Tier`. -/
instance tierBoundedOrder : BoundedOrder Dregg2.Finality.Tier where

/-- **Bridge: `commitAtMax` on `Tier` IS `Dregg2.Finality.crossTierJoin`.** The abstract
commit-as-join specialises (definitionally, since `Tier`'s `⊔` is `max`) to the concrete
cross-tier commit rule of the real finality module. So §4's derived no-downgrade /
monotonicity laws are laws of the actual system, not of a parallel abstraction. -/
theorem tier_commit_eq_crossTierJoin (a b : Dregg2.Finality.Tier) :
    commitAtMax a b = Dregg2.Finality.crossTierJoin a b := rfl

/-- **DERIVED at `Tier`: the concrete cross-tier commit never downgrades** — the §4
monotonicity, specialised to the real ladder. -/
theorem tier_crossTierJoin_no_downgrade (a b : Dregg2.Finality.Tier) :
    a ≤ Dregg2.Finality.crossTierJoin a b ∧ b ≤ Dregg2.Finality.crossTierJoin a b :=
  ⟨commitAtMax_le_left_def a b, commitAtMax_le_right_def a b⟩

end Finality

/-! # §5. I-confluence, DERIVED as a sub-join-semilattice (the third judgement).

`Dregg2.Confluence` *defines* `IConfluent I := ∀ x y, I x → I y → I (x ⊔ y)` over a
`MergeState`/`SemilatticeSup`. The categorical reading we DERIVE here: I-confluence is
exactly *"the coordination-free fragment `{x // I x}` is **closed under the invariant-merge
join** — a **sub-join-semilattice**."* The closure is not an extra hypothesis; it is what
makes the fragment a join-subalgebra, and we exhibit the sub-LUB structure. -/

section IConfluence

variable {S : Type u} [SemilatticeSup S]

/-- The third judgement (mirroring `Dregg2.Confluence.IConfluent`): an invariant `I` is
**I-confluent** iff concurrent invariant-preserving versions merge invariant-safely (BEC
Thm 3.1) — `I` is preserved by the `⊔` of the CvRDT merge-state. -/
def IConfluent (I : S → Prop) : Prop := ∀ x y, I x → I y → I (x ⊔ y)

/-- **Closed under the invariant-merge join** — the sub-(join-semi)lattice closure
condition: the fragment `{x // I x}` is stable under `⊔`. -/
def ClosedUnderJoin (I : S → Prop) : Prop := ∀ x y, I x → I y → I (x ⊔ y)

/-- **`iconfluent_eq_closed_def` — a definitional UNFOLD, not a derivation.** `IConfluent I`
and `ClosedUnderJoin I` are spelled out to the *same* proposition
(`∀ x y, I x → I y → I (x ⊔ y)`), so this `iff` holds by `Iff.rfl` — it does NOT *derive* one
notion from the other, it merely records that "I-confluence" and "closed-under-the-merge-join"
are two names for one condition. The genuine first-principles content of §5 is downstream: that
the fragment `{x // I x}` is a `SemilatticeSup` whose join is `confJoin` (`confJoin_lub`), and
the `Dregg2.Confluence` bridge (`tier1Eligible_closedUnderJoin`). -/
theorem iconfluent_eq_closed_def (I : S → Prop) : IConfluent I ↔ ClosedUnderJoin I :=
  Iff.rfl

/-- **The invariant-merge join on the coordination-free fragment.** Given I-confluence, two
in-fragment states merge to an in-fragment state — the `⊔` of `{x // I x}`, landing inside
`I` by closure. This is the binary join of the **sub-join-semilattice**. -/
def confJoin (I : S → Prop) (h : IConfluent I) (x y : {a // I a}) : {a // I a} :=
  ⟨x.1 ⊔ y.1, h x.1 y.1 x.2 y.2⟩

/-- **DERIVED: the fragment's join is the ambient join (inclusion is join-preserving).** The
sub-semilattice inclusion `{x // I x} ↪ S` preserves `⊔` — the merge of two coordination-free
states computed in the fragment agrees with the ambient CvRDT merge. The fragment is a
*genuine* sub-join-semilattice, not a re-merged copy. -/
theorem confJoin_incl (I : S → Prop) (h : IConfluent I) (x y : {a // I a}) :
    (confJoin I h x y).1 = x.1 ⊔ y.1 := rfl

/-- **DERIVED: the fragment join is a least upper bound (left/right bounds).** Each input is
below the merge — the merge dominates both concurrent versions, as a CvRDT join must. -/
theorem confJoin_le_left (I : S → Prop) (h : IConfluent I) (x y : {a // I a}) :
    x.1 ≤ (confJoin I h x y).1 := le_sup_left
theorem confJoin_le_right (I : S → Prop) (h : IConfluent I) (x y : {a // I a}) :
    y.1 ≤ (confJoin I h x y).1 := le_sup_right

/-- **DERIVED: the fragment join is the LEAST upper bound.** Any in-fragment state `z`
dominating both `x` and `y` dominates their merge — the merge is the *least* coordination-free
state above both. With the bounds above, this proves `confJoin` is the join of the
sub-semilattice, so `{x // I x}` is a `SemilatticeSup` whose join is `confJoin`. The
coordination-free fragment is exactly the join-subalgebra of `I`-confluence. -/
theorem confJoin_lub (I : S → Prop) (h : IConfluent I) (x y z : {a // I a})
    (hx : x.1 ≤ z.1) (hy : y.1 ≤ z.1) : (confJoin I h x y).1 ≤ z.1 :=
  sup_le hx hy

/-- **Bridge to `Dregg2.Confluence`.** A `Dregg2.Confluence.Tier1Eligible` invariant (the
real system's predicate for "runs coordination-free / tier-1") DERIVES the §5
closed-under-the-merge-join property: its coordination-free fragment is a genuine
sub-join-semilattice. We route through `Dregg2.Confluence.admits_sound` (the real module's
tier-1 soundness obligation), so §5's abstract derivation lands on the actual judgement —
tier-1 eligibility IS sub-semilattice closure. -/
theorem tier1Eligible_closedUnderJoin {S' : Type u} [Dregg2.Confluence.MergeState S']
    (I : Dregg2.Confluence.Invariant S') (h : Dregg2.Confluence.Tier1Eligible I) :
    ClosedUnderJoin (S := S') I :=
  fun x y hx hy => Dregg2.Confluence.admits_sound I h x y hx hy

end IConfluence

/-! # §3. The cell as a coalgebra; the hyperedge as a (wide) pullback.

`Dregg2.Boundary` *gives* the structure map `TurnCoalg.step : X → Obs × (Adm → X)`. We
state it here as a **coalgebra of an endofunctor** and the JointTurn/hyperedge binding as a
**pullback** (a limit), using mathlib's category-theoretic vocabulary, so that the cell's
defining property is a *universal property* rather than a chosen structure map. The
final-coalgebra existence (the anamorphism `νF`) is the one honest OPEN obligation. -/

section Coalgebra

variable {Obs Adm X Y Z : Type u}

/-- The **object action** of the behaviour endofunctor `F`, `F X = Obs × (Adm → X)` — a
Moore/DFA shape (output-on-state × input-indexed transition). This is `Dregg2.Boundary.F`
named as the action of an endofunctor on `Type u`. -/
def Fobj (Obs Adm X : Type u) : Type u := Obs × (Adm → X)

/-- The **morphism action** of the behaviour endofunctor `F` — its functorial lift of a map
`f : X → Y` to `F X → F Y` (relabel the successors by `f`, leave the observation fixed).
`Fobj`/`Fmap` together are the endofunctor `F : Type u → Type u`; the functor laws
`Fmap id = id` and `Fmap (g ∘ f) = Fmap g ∘ Fmap f` hold definitionally
(`Fmap_id`/`Fmap_comp`), so this is a *genuine* (if hand-spelled) endofunctor. We spell it
with plain functions rather than the bundled `Type u ⥤ Type u` because this mathlib slice
wraps `Type`-category morphisms in `ConcreteCategory.Fun`. -/
def Fmap (f : X → Y) : Fobj Obs Adm X → Fobj Obs Adm Y :=
  fun p => (p.1, fun a => f (p.2 a))

@[simp] theorem Fmap_id : Fmap (Obs := Obs) (Adm := Adm) (id : X → X) = id := rfl
@[simp] theorem Fmap_comp (g : Y → Z) (f : X → Y) :
    Fmap (Obs := Obs) (Adm := Adm) (g ∘ f) = Fmap g ∘ Fmap f := rfl

/-- **A cell IS an `F`-coalgebra** — a carrier `V` with a structure map `str : V → F V`.
This is the universal-property re-statement of `Dregg2.Boundary.TurnCoalg`: the structure
map is the defining datum of a coalgebra of the *endofunctor* `F = (Fobj, Fmap)`, rather
than an ad-hoc `step` record. (Spelled here rather than importing
`Mathlib.CategoryTheory.Endofunctor.Algebra` — not built in this lib's pinned mathlib
slice — but `str` IS the endofunctor-coalgebra structure map `V → F V`, and `CoalgHom`
below IS the coalgebra-morphism / functional-bisimulation condition.) -/
structure Cell (Obs Adm : Type u) where
  /-- The carrier (state space of cells). -/
  V : Type u
  /-- The endofunctor-coalgebra structure map `V → F V`. -/
  str : V → Fobj Obs Adm V

/-- The observation and successor of a cell-coalgebra, recovered from its structure map
(matching `TurnCoalg.obs`/`TurnCoalg.next`). -/
def Cell.obs (c : Cell Obs Adm) (x : c.V) : Obs := (c.str x).1
def Cell.next (c : Cell Obs Adm) (x : c.V) (a : Adm) : c.V := (c.str x).2 a

/-- **A coalgebra morphism / functional bisimulation** `c ⟶ d`: a carrier map `f` that
commutes with the structure maps (`F.map f ∘ c.str = d.str ∘ f`). This is the precise
"behaviour-preserving map" condition that the category of `F`-coalgebras imposes — a
*functional bisimulation* between cells. -/
structure CoalgHom (c d : Cell Obs Adm) where
  /-- The underlying carrier map. -/
  f : c.V → d.V
  /-- The coalgebra-square: `f` intertwines the two structure maps. -/
  commutes : Fmap f ∘ c.str = d.str ∘ f

/-- **Coalgebra reachability is the cell's life: every cell is behaviourally equivalent to
itself.** The identity carrier map is a coalgebra morphism (the square commutes
definitionally, `Fmap_id`), so every cell bisimulates itself — the categorical source of
`Dregg2.Boundary.sound_refl`. -/
theorem cell_self_bisim (c : Cell Obs Adm) :
    ∃ h : CoalgHom c c, h.f = id :=
  ⟨⟨id, by simp⟩, rfl⟩

/-! ### The hyperedge / JointTurn as a wide pullback (a limit).

`Dregg2.JointTurn`/`Dregg2.Hyperedge` bind several cells into one atomic joint turn. The
categorical content: the *joint state space* over a shared interface is the **pullback** of
the participating cells' projections to that interface — and a many-participant hyperedge is
the **wide pullback** (the limit of the wide-cospan of projections). We state the universal
property faithfully via mathlib `IsPullback`. -/

variable {𝒞 : Type u} [Category.{v} 𝒞]

/-- **The two-party JointTurn binding, stated as a pullback universal property.** Given two
participant objects `P₁ P₂` with projections `π₁ π₂` to a shared interface `I`, the bound
*joint* object `J` with its two legs `j₁ j₂` is characterised by being a **pullback**: it is
the universal object whose two views agree on the interface (`j₁ ≫ π₁ = j₂ ≫ π₂`) and
through which every other agreeing pair factors uniquely. This is the precise sense in which
"a JointTurn is the atomic binding of two cells over their shared boundary." We *state* the
property (as the `IsPullback` predicate) rather than postulate a chosen `J`. -/
def IsJointTurn {I P₁ P₂ J : 𝒞} (j₁ : J ⟶ P₁) (j₂ : J ⟶ P₂)
    (π₁ : P₁ ⟶ I) (π₂ : P₂ ⟶ I) : Prop :=
  IsPullback j₁ j₂ π₁ π₂

/-- **The pullback square of a JointTurn commutes (DERIVED from the universal property).**
If `J` is the joint binding of `P₁,P₂` over `I`, the two participants' views of the interface
agree: `j₁ ≫ π₁ = j₂ ≫ π₂`. This is "the bound cells share a consistent boundary," read off
the `IsPullback` predicate (`IsPullback.w`) — not assumed separately. -/
theorem jointTurn_interface_agrees {I P₁ P₂ J : 𝒞}
    {j₁ : J ⟶ P₁} {j₂ : J ⟶ P₂} {π₁ : P₁ ⟶ I} {π₂ : P₂ ⟶ I}
    (h : IsJointTurn j₁ j₂ π₁ π₂) : j₁ ≫ π₁ = j₂ ≫ π₂ :=
  h.w

/-- **The JointTurn is universal (DERIVED): every consistent pair of views factors through
it.** For any object `W` with views `w₁ : W ⟶ P₁`, `w₂ : W ⟶ P₂` that agree on the interface
(`w₁ ≫ π₁ = w₂ ≫ π₂`), there is a unique mediating map `W ⟶ J` recovering both views. This
is the *binding is canonical* property — the atomic joint turn is determined, not chosen.
It is the pullback `lift`/uniqueness, read off `IsPullback`. -/
theorem jointTurn_universal {I P₁ P₂ J : 𝒞}
    {j₁ : J ⟶ P₁} {j₂ : J ⟶ P₂} {π₁ : P₁ ⟶ I} {π₂ : P₂ ⟶ I}
    (h : IsJointTurn j₁ j₂ π₁ π₂)
    {W : 𝒞} (w₁ : W ⟶ P₁) (w₂ : W ⟶ P₂) (hw : w₁ ≫ π₁ = w₂ ≫ π₂) :
    ∃ m : W ⟶ J, m ≫ j₁ = w₁ ∧ m ≫ j₂ = w₂ :=
  ⟨h.lift w₁ w₂ hw, h.lift_fst w₁ w₂ hw, h.lift_snd w₁ w₂ hw⟩

/-- **The mediator is UNIQUE (DERIVED).** Two maps `W ⟶ J` that both reproduce the
participants' views agree — the *binding is canonical* in the strong (uniqueness) sense,
read off `IsPullback.hom_ext`. Together with `jointTurn_universal` this is the full
existence-and-uniqueness universal property of the two-party hyperedge. -/
theorem jointTurn_mediator_unique {I P₁ P₂ J : 𝒞}
    {j₁ : J ⟶ P₁} {j₂ : J ⟶ P₂} {π₁ : P₁ ⟶ I} {π₂ : P₂ ⟶ I}
    (h : IsJointTurn j₁ j₂ π₁ π₂)
    {W : 𝒞} {m m' : W ⟶ J}
    (e₁ : m ≫ j₁ = m' ≫ j₁) (e₂ : m ≫ j₂ = m' ≫ j₂) : m = m' :=
  h.hom_ext e₁ e₂

/-! ### The N-ary hyperedge as a *wide* pullback (a limit over `TurnId`).

The binary `IsJointTurn` is the two-participant case. A real hyperedge binds **N**
participants — indexed by a `TurnId`-shaped type `ι` — into one atomic joint turn over the
shared interface `I`. The categorical content is the **wide pullback**: the limit of the
wide cospan `(πᵢ : Pᵢ ⟶ I)ᵢ`. We state its universal property *by hand* (rather than via
mathlib's `HasWidePullback`, which would demand a limit-existence instance) as a faithful
cone-with-unique-mediator **witness bundle** (the `lift` mediator is genuine *data*, so the
bundle is `Type`-valued — exactly the limit-cone data — while `agree`/`fac`/`uniq` are its
universal-property laws), mirroring `IsPullback` for arbitrary arity. This is
the honest N-ary generalisation of `IsJointTurn`.

`ι` plays the role of `TurnId` (the participant index); `mathlib`'s
`WidePullbackShape ι = Option ι` is exactly this diagram shape (the `none` apex is the
interface `I`, the `some i` are the participants `Pᵢ`), and our cone legs `legs i` are its
`π`. We give the predicate directly so the universal property is self-contained. -/

/-- **An N-ary joint turn (wide-pullback cone with unique mediator).** A bound object `J`
with legs `legs i : J ⟶ Pᵢ` into the `ι`-indexed participants is the hyperedge over the
interface projections `proj i : Pᵢ ⟶ I` iff:
* **(agree)** all participants' views of the interface coincide: every `legs i ≫ proj i` is
  one and the same arrow `J ⟶ I` (the bound cells share a *single* consistent boundary), and
* **(universal)** every other object `W` whose `ι`-indexed views agree on the interface
  factors through `J` by a **unique** mediator.

This is the wide pullback's universal property, arity `ι`. -/
structure IsWideJointTurn {ι : Type w} {I J : 𝒞} (P : ι → 𝒞)
    (legs : ∀ i, J ⟶ P i) (proj : ∀ i, P i ⟶ I) where
  /-- All participants agree on the interface: a single shared boundary arrow `J ⟶ I`. -/
  agree : ∀ i i', legs i ≫ proj i = legs i' ≫ proj i'
  /-- Existence of the mediator for any agreeing cone `(W, views)`. -/
  lift {W : 𝒞} (views : ∀ i, W ⟶ P i)
    (hv : ∀ i i', views i ≫ proj i = views i' ≫ proj i') : W ⟶ J
  /-- The mediator reproduces every view. -/
  fac {W : 𝒞} (views : ∀ i, W ⟶ P i)
    (hv : ∀ i i', views i ≫ proj i = views i' ≫ proj i') (i : ι) :
    lift views hv ≫ legs i = views i
  /-- The mediator is unique: any two maps reproducing all views agree. -/
  uniq {W : 𝒞} {m m' : W ⟶ J} (e : ∀ i, m ≫ legs i = m' ≫ legs i) : m = m'

variable {ι : Type w}

/-- **DERIVED: the N-ary interface is globally consistent.** From the wide-pullback datum,
every pair of bound participants sees the same interface — the hyperedge's defining
"single shared boundary across all N cells," read off the `agree` field. -/
theorem wideJointTurn_interface_agrees {I J : 𝒞} {P : ι → 𝒞}
    {legs : ∀ i, J ⟶ P i} {proj : ∀ i, P i ⟶ I}
    (h : IsWideJointTurn P legs proj) (i i' : ι) :
    legs i ≫ proj i = legs i' ≫ proj i' :=
  h.agree i i'

/-- **DERIVED: the N-ary hyperedge is universal.** Any object `W` with `ι`-indexed views
that pairwise agree on the interface factors through the bound `J` by a mediator
reproducing every view. The atomic N-party joint turn is *determined*, not chosen — the
full wide-pullback `lift`/`fac`. -/
theorem wideJointTurn_universal {I J : 𝒞} {P : ι → 𝒞}
    {legs : ∀ i, J ⟶ P i} {proj : ∀ i, P i ⟶ I}
    (h : IsWideJointTurn P legs proj)
    {W : 𝒞} (views : ∀ i, W ⟶ P i)
    (hv : ∀ i i', views i ≫ proj i = views i' ≫ proj i') :
    ∃ m : W ⟶ J, ∀ i, m ≫ legs i = views i :=
  ⟨h.lift views hv, h.fac views hv⟩

/-- **DERIVED: the N-ary mediator is unique** — the wide-pullback `uniq`, the strong-binding
canonicity for arbitrary arity. With `wideJointTurn_universal` this is the complete
existence-and-uniqueness universal property of the hyperedge. -/
theorem wideJointTurn_mediator_unique {I J : 𝒞} {P : ι → 𝒞}
    {legs : ∀ i, J ⟶ P i} {proj : ∀ i, P i ⟶ I}
    (h : IsWideJointTurn P legs proj)
    {W : 𝒞} {m m' : W ⟶ J} (e : ∀ i, m ≫ legs i = m' ≫ legs i) : m = m' :=
  h.uniq e

/-- **The binary `IsJointTurn` is the `ι := Bool` (two-participant) wide pullback (DERIVED).**
A genuine `IsPullback` square refines to the N-ary `IsWideJointTurn` at `ι = Bool`: the
wide pullback specialises to the ordinary pullback, so `IsWideJointTurn` is a *faithful*
generalisation — the binary case is not lost, it is `N = 2`. -/
noncomputable def isJointTurn_to_wide {I P₁ P₂ J : 𝒞}
    {j₁ : J ⟶ P₁} {j₂ : J ⟶ P₂} {π₁ : P₁ ⟶ I} {π₂ : P₂ ⟶ I}
    (h : IsJointTurn j₁ j₂ π₁ π₂) :
    IsWideJointTurn (ι := Bool) (I := I) (J := J)
      (fun b => match b with | true => P₂ | false => P₁)
      (fun b => match b with | true => j₂ | false => j₁)
      (fun b => match b with | true => π₂ | false => π₁) where
  agree i i' := by
    cases i <;> cases i' <;> first | rfl | exact h.w | exact h.w.symm
  lift views hv := h.lift (views false) (views true) (hv false true)
  fac views hv i := by
    cases i
    · exact h.lift_fst (views false) (views true) (hv false true)
    · exact h.lift_snd (views false) (views true) (hv false true)
  uniq {W m m'} e := h.hom_ext (e false) (e true)

/-! ### §3 deepened: the final coalgebra `νF` — advancing the OPEN.

Even with `νF`'s *existence* still open, we can prove most of its *structure*: what it
would mean to be terminal, that the anamorphism (unfold) is **unique** if it exists, and
that coinduction IS the terminal universal property. This sharpens the OPEN from "does a
final coalgebra exist?" to "here is its universal property, fully stated and its
uniqueness proved; only the *construction* of the carrier remains." -/

/-- **Coalgebra morphism composition** — the category of `F`-coalgebras has composition.
(Identity is `cell_self_bisim`.) We need it to state finality. -/
def CoalgHom.comp {c d e : Cell Obs Adm} (g : CoalgHom d e) (f : CoalgHom c d) :
    CoalgHom c e where
  f := g.f ∘ f.f
  commutes := by
    have hf := f.commutes; have hg := g.commutes
    -- Fmap (g∘f) = Fmap g ∘ Fmap f, then paste the two squares.
    rw [Fmap_comp]
    calc (Fmap g.f ∘ Fmap f.f) ∘ c.str
        = Fmap g.f ∘ (Fmap f.f ∘ c.str) := by rfl
      _ = Fmap g.f ∘ (d.str ∘ f.f) := by rw [hf]
      _ = (Fmap g.f ∘ d.str) ∘ f.f := by rfl
      _ = (e.str ∘ g.f) ∘ f.f := by rw [hg]
      _ = e.str ∘ (g.f ∘ f.f) := by rfl

/-- **`IsFinalCell νF` — the terminal `F`-coalgebra universal property, stated.** `νF` is
final iff from *every* cell `c` there is a coalgebra morphism into it (the **anamorphism**
`ana c`), and any two such morphisms agree (**uniqueness** — the heart of coinduction).
This is `Dregg2.Boundary`'s "live codata into which every behaviour unfolds" as a precise
predicate; the OPEN below is only whether such a `νF` *exists*. -/
structure IsFinalCell (νF : Cell Obs Adm) : Prop where
  /-- The anamorphism: every cell unfolds into `νF`. -/
  ana : ∀ c : Cell Obs Adm, Nonempty (CoalgHom c νF)
  /-- Uniqueness: any two coalgebra morphisms `c ⟶ νF` have equal carrier maps. -/
  uniq : ∀ {c : Cell Obs Adm} (g h : CoalgHom c νF), g.f = h.f

/-- **DERIVED: the anamorphism is unique (coinduction).** If `νF` is final, then for every
cell the unfold into `νF` is a `Subsingleton` of carrier maps — there is *at most one*
behaviour-preserving map into the final coalgebra. This **uniqueness** is exactly the
coinduction principle: two states with the same `νF`-image are behaviourally equal. We
prove it *conditionally* on finality (the genuine content), leaving only existence open. -/
theorem ana_unique {νF : Cell Obs Adm} (hfin : IsFinalCell νF) (c : Cell Obs Adm) :
    ∀ g h : CoalgHom c νF, g.f = h.f :=
  fun g h => hfin.uniq g h

/-- **DERIVED: `νF` is unique up to the carrier maps it forces (terminal objects are
essentially unique).** If two cells are *both* final, the anamorphisms between them compose
to the identity on carriers — they are mutually inverse functional bisimulations, hence the
final behaviour is canonical. We extract the round-trip carrier equation (`ana ∘ ana = id`),
the computational core of terminal-uniqueness, from `uniq` applied to the two endomorphism
candidates `ana_{c→c}` and `𝟙`. -/
theorem final_unique_roundtrip {ν₁ ν₂ : Cell Obs Adm}
    (h₁ : IsFinalCell ν₁) (h₂ : IsFinalCell ν₂)
    (a₁₂ : CoalgHom ν₁ ν₂) (a₂₁ : CoalgHom ν₂ ν₁) :
    a₂₁.f ∘ a₁₂.f = id := by
  -- `a₂₁ ∘ a₁₂ : ν₁ ⟶ ν₁` and the identity are both coalg-morphisms `ν₁ ⟶ ν₁`;
  -- finality of `ν₁` forces their carriers equal.
  have := h₁.uniq (CoalgHom.comp a₂₁ a₁₂) ⟨id, by simp⟩
  simpa [CoalgHom.comp] using this

/-
OPEN (`§3`, the anamorphism / final-coalgebra **existence** — now SHARPENED). The cell type
`Dregg2.Boundary` *wants* is the **final** `behaviour`-coalgebra `νF` — the unique behaviour
into which every coalgebra anamorphs (the "live codata, never bottoms out" of `§2`).

What is now PROVED (no longer open): the universal property is fully stated (`IsFinalCell`),
its **uniqueness half is a theorem** — the anamorphism is unique (`ana_unique`, the
coinduction principle) and the final object is canonical up to a carrier round-trip
(`final_unique_roundtrip`), both *conditional on finality*, which is the genuine categorical
content of coinduction. The category of `F`-coalgebras has identities (`cell_self_bisim`)
and composition (`CoalgHom.comp`). The hyperedge has its (wide) pullback universal property
PROVED (`wideJointTurn_universal`/`wideJointTurn_mediator_unique`).

What remains OPEN is **strictly the construction of the carrier** — an *inhabitant* of
`IsFinalCell` for `F X = Obs × (Adm → X)`:

    ∃ νF : Cell Obs Adm, IsFinalCell νF

The precise named categorical lemma the construction needs is one of:
  * **Adámek's terminal-coalgebra theorem** — `νF = lim (… → F²1 → F1 → 1)`, the limit of
    the ω^op-chain of `F`-iterates of the terminal object, which converges because
    `F X = Obs × (Adm → X)` preserves ω^op-limits (it is a finite product of a constant and
    a representable, both continuous); or
  * a **guarded-recursion `▷` backend** giving `νF` as a coinductive type directly.
Either is a module of its own (needs `CategoryTheory.Limits` ω-chains, not built here as a
ready `HasLimit` instance for this `F`). We do NOT axiomatize it; we have moved the OPEN from
"what is `νF`?" to "construct the carrier; its universal property and uniqueness are done."
The behavioural content the system actually uses — bisimulation-as-coalgebra-morphism,
reflexivity, composition, and the step-completeness safety invariant — is already proved
(`cell_self_bisim`/`CoalgHom.comp`/`ana_unique` here; `stepComplete_preserves` in
`Dregg2.Boundary`) without needing `νF` to exist. Concretely the missing existence fact is:

    a terminal object `νF` in the category `(Cell Obs Adm, CoalgHom)` exists

— i.e. a cell `νF` together with, for every cell `c`, a UNIQUE coalgebra morphism
`anaF c : CoalgHom c νF` — from which the anamorphism and its uniqueness (the coinduction
principle underlying `Dregg2.Boundary.IsBisim`) would follow. We do NOT axiomatize it; we
record it as the precise open hypothesis the full derivation still needs. The *behavioural*
content the system actually uses — bisimulation-as-coalgebra-morphism, reflexivity, and the
step-completeness safety invariant — is already proved (`cell_self_bisim` here;
`stepComplete_preserves` in `Dregg2.Boundary`) without needing `νF` to exist. -/

end Coalgebra

/-! # §6. The boundary law as a square — tying the verify-seam (§2) to the cell (§3).

§2 derived the verify/find seam as a `GaloisConnection realizes ⊣ verifies`; §3 derived the
cell as an `F`-coalgebra with observation `Cell.obs`. They meet at the **cell boundary**: a
cell observes a *demand*, and each state is backed by a *supply*. The "boundary law" of
`Dregg2.Boundary` — that a cell's observation is *consistent with* what its supply verifies —
is DERIVED here as a **commuting square** that is *precisely the seam adjunction read at the
coalgebra's observation*. No separate boundary postulate: §3's observation passes through
§2's adjunction by construction. -/

section Boundary

variable {Demand Supply Adm : Type u} [Preorder Demand] [PartialOrder Supply]

/-- **The cell-boundary square (the §2⊗§3 datum).** A cell `c` whose observation is a
*demand*, equipped with a backing-supply map `adm : c.V → Supply` (the witness/supply each
state holds), is **seam-consistent** at the seam `S` iff its boundary obeys the adjunction:
whenever the demand a state observes is realized by its supply (`realizes (adm x) ≤ obs x`),
that supply suffices to verify the observation (`adm x ≤ verifies (obs x)`). This is the
square `realizes ⊣ verifies` *transported along the coalgebra's observation*. -/
def SeamConsistent (S : Seam (Demand := Demand) (Supply := Supply))
    (c : Cell Demand Adm) (adm : c.V → Supply) : Prop :=
  ∀ x : c.V, S.realizes (adm x) ≤ c.obs x → adm x ≤ S.verifies (c.obs x)

/-- **DERIVED: every cell is seam-consistent — the boundary square commutes for free.** The
cell-boundary law is *exactly* the seam adjunction `realizes s ≤ d ↔ s ≤ verifies d` read at
`d := c.obs x`, `s := adm x`. So §3's coalgebra and §2's Galois seam **agree at the
boundary by construction**: the boundary law is not an extra axiom, it is the adjunction. -/
theorem seamConsistent_of_adj (S : Seam (Demand := Demand) (Supply := Supply))
    (c : Cell Demand Adm) (adm : c.V → Supply) : SeamConsistent S c adm :=
  fun x h => (S.adj (adm x) (c.obs x)).mp h

/-- **DERIVED: the boundary closure square is idempotent at every observation.** Re-running
the verify→realize seam on a cell's observation reaches a fixed point in one round — the
seam closure (`seam_closure_idem`) instantiated at the coalgebra's `obs`. The cell boundary
*stabilises*: a once-verified observation needs no re-verification across turns. -/
theorem seam_boundary_closure (S : Seam (Demand := Demand) (Supply := Supply))
    (c : Cell Demand Adm) (x : c.V) :
    S.verifies (S.realizes (S.verifies (S.realizes (S.verifies (c.obs x)))))
      = S.verifies (S.realizes (S.verifies (c.obs x))) :=
  S.adj.u_l_u_eq_u (S.realizes (S.verifies (c.obs x)))

end Boundary

/-! # Axiom-hygiene: pin the DERIVED keystones as kernel-clean. -/

-- §1 conservation, derived from the lax monoidal functor:
#assert_axioms measure_unit
#assert_axioms measure_tensor
#assert_axioms measure_invariant
#assert_axioms no_free_copy
#assert_axioms conservation_core_derived

-- §2 the verify/find seam, derived from the Galois connection:
#assert_axioms seam_attenuate_monotone
#assert_axioms seam_realizes_monotone
#assert_axioms seam_unit
#assert_axioms seam_counit
#assert_axioms seam_closure_idem
#assert_axioms seam_roundtrip

-- §3 the cell coalgebra & the hyperedge pullback (universal properties):
#assert_axioms Fmap_id
#assert_axioms Fmap_comp
#assert_axioms cell_self_bisim
#assert_axioms jointTurn_interface_agrees
#assert_axioms jointTurn_universal
#assert_axioms wideJointTurn_universal
#assert_axioms wideJointTurn_mediator_unique
#assert_axioms ana_unique

-- §4 finality: the mathlib lattice laws specialize to the Tier order. The load-bearing exports
-- are `commit_monotone` and the `Tier`-touching `tier_commit_eq_crossTierJoin` /
-- `tier_crossTierJoin_no_downgrade`; the `commitAtMax_*_def` lemmas are join-unfolds beneath them.
#assert_axioms commitAtMax_le_left_def
#assert_axioms commit_monotone
#assert_axioms tier_commit_eq_crossTierJoin
#assert_axioms tier_crossTierJoin_no_downgrade

-- §5 I-confluence, derived as a sub-join-semilattice (closed-under-⊔):
#assert_axioms iconfluent_eq_closed_def
#assert_axioms confJoin_incl
#assert_axioms confJoin_lub
#assert_axioms tier1Eligible_closedUnderJoin

-- §6 the boundary law as a square (the seam adjunction ⊗ the cell coalgebra):
#assert_axioms seamConsistent_of_adj
#assert_axioms seam_boundary_closure

/-! # Coda — how this moves the spec from postulated toward derived.

`Dregg2.Core.Conservation` postulates `unit_zero`/`tensor_add` as *fields*; here
(`measure_unit`/`measure_tensor`) they are **theorems** about a lax monoidal functor
`Σ : C ⥤ Discrete M`, and `withholding_no_free_copy` has a **categorical proof**
(`no_free_copy`) from *(comonoid copy map) + (cancellative discrete target)*. `Dregg2.Laws`
constructs the `Predicate ⊣ Witness` connection; here its operational laws (attenuation,
round-trips, closure) are **consequences** of the seam's defining `GaloisConnection`.
`Dregg2.Boundary` gives a structure map; here the cell is an `F`-coalgebra and the hyperedge
a **pullback** — now also a **wide pullback** for N participants (`wideJointTurn_universal`/
`wideJointTurn_mediator_unique`) — with the binding's universal property PROVED and only the
final-coalgebra existence (`νF`) honestly OPEN (its uniqueness/coinduction, `ana_unique`, is
proved *conditionally on finality*).

**The three judgements, each now a categorical structure.** §1 conservation is
*substructurality* — the absence of a natural diagonal `Δ`/discard is conservation
(`diagonal_collapses_measure`/`no_free_discard`, the linear/affine reading). §4 derives
`Dregg2.Finality`'s **second judgement** (ordering/finality) as a **bounded lattice**: the
cross-tier commit is the lattice *join* (`commitAtMax = crossTierJoin`), *no-downgrade IS
monotonicity* (`commit_monotone`), and the ladder is bounded (`tierBoundedOrder`, with the
derived `OrderTop`/`OrderBot` `Dregg2` leaves implicit) — the mathlib lattice/`BoundedOrder`
laws specializing to the Tier order, the `commitAtMax_*_def` lemmas being join-unfolds beneath
the `Tier`-touching results. §5 derives `Dregg2.Confluence`'s **third judgement** (I-confluence)
as a **sub-join-semilattice**: `IConfluent` and `closed-under-⊔` are the same condition under
two names (`iconfluent_eq_closed_def`, a definitional unfold), with the coordination-free
fragment exhibited as a
join-subalgebra (`confJoin`/`confJoin_lub`) and tier-1 eligibility shown to BE that closure
(`tier1Eligible_closedUnderJoin`). §6 ties §2⊗§3: the **cell-boundary law is the seam
adjunction read at the coalgebra's observation** (`seamConsistent_of_adj`) — not an extra
postulate, the adjunction itself.

The honest caveat (`study-category §5`): the conservation derivation's target is *discrete*,
so it is **thin** — what is genuinely derived is *monoid-hom + invariance*, the real content
the `Dregg2.Core` docstring already names; the "strong monoidal functor" packaging is
decorative and we do not oversell it. The §4/§5 lattice derivations are honest order theory
(no thinness caveat); the §6 boundary square is the genuine adjunction, faithfully
transported. The ONE deep OPEN remains the final-coalgebra *existence* (Adámek / guarded
recursion), with its universal property and uniqueness already proved. This is a START at
"the abstract spec is derived from categorical first principles," substantially advanced —
all three judgements are now derived structures, not postulates — but not the finished
derivation. -/

end Metatheory

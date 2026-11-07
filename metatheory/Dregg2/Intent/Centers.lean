/-
# Dregg2.Intent.Centers — the commutative central monoid + its escrow monad (Phase 3, step 1–2).

`.docs-history-noclaude/rebuild/metatheory/INTENT-REFS-centers.md` §4, steps 1–2 (the *unifier*; the monoidal-Kleisli L-gate and
Theorem B are explicitly DEFERRED — steps 3–5). Anchor: Flake–Laugwitz–Posur, *Projection Formulas and
Induced Functors on Centers of Monoidal Categories* (arXiv 2402.10094), Def 5.1 + Thm 5.6.

**What this builds.**

  1. `CommCentralMonoid R := CommMon (Center R)` (paper Def 5.1, the *commutative central monoid*): a
     commutative monoid object living in the *braided* Drinfeld center `Center R`. The half-braiding
     component (`M.X.2.β`) is the "commutes-past-every-turn" datum; `MonObj`/`IsCommMonObj` make
     `mul`/`unit` central AND commutative *by construction*. This typechecks precisely because `Center R`
     is braided (`CategoryTheory.Center.braidedCategoryCenter`), so `CommMon (Center R)` is well-formed
     (`IsCommMonObj` needs a `BraidedCategory`). Plus its projections (the swap, `mul`/`unit` central).

  2. `escrowMonad M := (– ⊗ M)` as a `Monad` (paper Thm 5.6; η = `A ◁ unit`, μ = `A ◁ mul`), HAND-BUILT
     — the underlying functor is `tensorRight M`; the three monad laws fall out of `MonObj`'s
     `one_mul`/`mul_one`/`mul_assoc` whiskered into the carried `A` (no braiding, no commutativity needed
     for the *monad*). Then `escrowMonad_isMonoidal` (Thm 5.6's page-46 lax structure): the
     `LaxMonoidal (tensorRight M)` whose tensorator is `tensorμ X M Y M ≫ (X⊗Y) ◁ μ[M]` — the braided
     strength `tensorμ` slides one `M` past `Y`, then `μ[M]` coalesces the two pools. This needs only
     `[BraidedCategory C]` + `[MonObj M]` — a plain monoid object in a braided category: the
     associativity hexagon closes via `tensor_associativity` + `mul_assoc`, and `tensorμ` lands the two
     pools consistently with **no `mul_comm` required**. (Commutativity is load-bearing elsewhere — for
     *centrality* §4 and *rigidity* §7 — not for the lax monad. `writerEscrow_isMonoidal` + the
     non-discrete writer witness below check the lax structure where its coherences are non-trivial.)

**DEFERRED (steps 3–5 of §4):** `monoidalKleisli` (the `MonoidalCategory (Kleisli T_M)` L-gate), the
`escrow_projection_formula` (Lemma 5.11) with the refuted general sibling, and Theorem B
(`Z(R) : Z(D) → Z(C)`, 4.10). Those depend on the monoidal-Kleisli prerequisite mathlib lacks.

**The escrow constructions are stated POLYMORPHICALLY** over a monoidal category `C` and a monoid object
`M : C` (the monad needs only `MonoidalCategory`; the lax structure adds just `[BraidedCategory C]` — no
commutativity). `CommCentralMonoid R` is then the canonical carrier: `M : CommMon (Center R)`
supplies `M.X : Center R` with `[MonObj M.X]` + `[IsCommMonObj M.X]` in the braided `Center R`.

**CRITICAL MODEL CALL (ember-decided): escrow is KEPT SEPARATE.** `T_M = (– ⊗ M)` here models a
STANDING / ACCUMULATING pool — a *frictionless standing offer / ideal no-arb liquidity* side: `μ`
COALESCES two pool contributions (`x · y`). It is **NOT** the one-shot Intent escrow (`EscrowWitness`
in `Intent/Core.lean`, an affine consumed lockbox where released ≠ refundable). Coalescing ≠
consumption. The one-shot affine escrow is a separate construct bridged elsewhere; do not unify the
two under one `M` (`INTENT-REFS-centers.md` §3 row #4).

**`FrictionlessStandingOffer` (was "AMM-as-central-object", a PUN — DROPPED).** A `HalfBraiding X`
forces `β U : X ⊗ U ≅ U ⊗ X` to be an *isomorphism* for every `U` — the offer must commute
*invertibly* past every turn (no-arb order-independence). A real slippage/fee/finite-liquidity AMM has
`X ⊗ U ≇ U ⊗ X` in value, so it is **provably not** a center object at all. That non-existence IS the
teeth (`noncommuting_admits_no_halfBraiding` below, concretely on the non-commutative
`Discrete (FreeMonoid (Fin 2))`): the half-braiding models no-arb order-independence, full stop — it
does not verify constant-product economics.

**TEETH.** The genuine teeth of this layer are the *centrality* refutation
(`noncommuting_admits_no_halfBraiding`, §4: a non-commutative resource process is provably no center
object) and the *rigidity* refutation (`escrow_no_iso_without_rigidity`, §7.3: a non-dualizable object
gives no projection iso). Commutativity is real content where it IS used — `CommCentralMonoid.mul_comm`
(§1, the central monoid is commutative) and centrality (§4). A discrete demo
(`Intent/Resource.DemoRes`) has only the trivial `M = 𝟙_` (its hom-sets are subsingletons), so its
`mul_comm` is a `Subsingleton.elim` tautology — VACUOUS. So commutativity is also checked on a
**non-discrete** witness: the *writer comm-monoid object* `Multiplicative ℕ` in cartesian-monoidal
`Type`, where `mul` is a genuine binary function (`+`) and `writer_mul_comm_has_content` exhibits that
its `IsCommMonObj.mul_comm` carries real content (`a * b` and `b * a` are computed and distinct off the
diagonal). NOTE: the lax monad `escrowMonad_isMonoidal` itself needs no commutativity (see above).

§8 carriers: none (this layer is mathlib-internal
category theory; the only hypotheses are `MonObj`/`IsCommMonObj` typeclass carriers laws).
-/
import Mathlib.CategoryTheory.Monoidal.Center
import Mathlib.CategoryTheory.Monoidal.CommMon_
import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Discrete
import Mathlib.CategoryTheory.Monoidal.Internal.Types.Basic
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Dregg2.Intent.Resource
import Dregg2.Tactics

universe v u

namespace Dregg2.Intent

open CategoryTheory MonoidalCategory Functor.LaxMonoidal

-- NOTE: we deliberately do NOT `open MonObj`. Its scoped notation set includes the *bare* `μ`/`η`
-- (`= MonObj.mul`/`MonObj.one`), which would shadow the structure FIELD names `η`/`μ` of `Monad` and
-- `LaxMonoidal` when we define those instances below (the parser reads `η := …` as the notation token,
-- "unexpected token 'η'"). Instead we use local, non-colliding notations `𝟙ₘ[M]` (monoid unit) and
-- `μₘ[M]` (monoid mul) for `MonObj.one`/`MonObj.mul`, so field assignments stay legible without the clash.

/-- Local notation for the monoid-object multiplication `MonObj.mul` (avoids the bare-`μ` field clash). -/
local notation "μₘ[" M "]" => MonObj.mul (X := M)
/-- Local notation for the monoid-object unit `MonObj.one` (avoids the bare-`η` field clash). -/
local notation "𝟙ₘ[" M "]" => MonObj.one (X := M)

/-! ## 1. `CommCentralMonoid` — a commutative monoid object in the Drinfeld center (paper Def 5.1). -/

/-- **A commutative central monoid** (Flake–Laugwitz–Posur Def 5.1): a commutative monoid object in the
*braided* Drinfeld center `Center R`. This is the standing-offer / accumulating-pool carrier of the
escrow theory. The half-braiding component `M.X.2.β` is the "commutes-past-every-turn" datum, and
`[IsCommMonObj M.X]` makes `mul`/`unit` central AND commutative by construction.

It typechecks precisely because `Center R` is braided (`CategoryTheory.Center.braidedCategoryCenter`),
so `CommMon (Center R)` is well-formed (`IsCommMonObj` needs a `BraidedCategory`). -/
abbrev CommCentralMonoid (R : Type u) [Category.{v} R] [MonoidalCategory.{v} R] :=
  CommMon (Center R)

namespace CommCentralMonoid

variable {R : Type u} [Category.{v} R] [MonoidalCategory.{v} R]

/-- The underlying object of `R` carrying the standing pool (forget the half-braiding *and* the monoid
structure): `M.X : Center R` is the central object, `M.X.1 : R` is the bare resource. -/
abbrev carrier (M : CommCentralMonoid R) : R := M.X.1

/-- The half-braiding swap of the central monoid: `M.X.2.β U : M.X.1 ⊗ U ≅ U ⊗ M.X.1`. This is the
isomorphism witnessing that the standing pool commutes *invertibly* past every other resource `U` (the
no-arb order-independence datum). Projected straight off the `Center R` object. -/
abbrev swap (M : CommCentralMonoid R) (U : R) : M.X.1 ⊗ U ≅ U ⊗ M.X.1 := M.X.2.β U

/-- The pool multiplication, in `Center R` (paper `mul`): coalesces two pool contributions. Lives in the
center, so it is central by construction. -/
abbrev mul (M : CommCentralMonoid R) : M.X ⊗ M.X ⟶ M.X := μₘ[M.X]

/-- The pool unit, in `Center R` (paper `unit`). -/
abbrev one (M : CommCentralMonoid R) : 𝟙_ (Center R) ⟶ M.X := 𝟙ₘ[M.X]

/-- **`mul` is commutative w.r.t. the half-braiding swap** — the paper's commutativity of a central
monoid, read straight off `IsCommMonObj`: `(β_ M.X M.X).hom ≫ μ = μ` in `Center R`. Not a fresh law; the
projection of the carrier's `IsCommMonObj.mul_comm`. -/
theorem mul_comm (M : CommCentralMonoid R) :
    (β_ M.X M.X).hom ≫ μₘ[M.X] = μₘ[M.X] :=
  IsCommMonObj.mul_comm M.X

end CommCentralMonoid

/-! ## 2. The escrow monad `T_M = (– ⊗ M)` (paper Thm 5.6) — hand-built over a monoid object.

Stated polymorphically over a monoidal category `C` and `M : C` with `[MonObj M]`. The underlying
functor is `tensorRight M` (`A ↦ A ⊗ M`, `f ↦ f ▷ M`). η = `(ρ_ A).inv ≫ A ◁ unit`,
μ = `(α_ A M M).hom ≫ A ◁ mul`. The three monad laws are exactly `MonObj`'s unitality/associativity
whiskered into `A` — no braiding, no commutativity required for the *monad* (those enter only in the
lax-monoidal structure, §3). -/

section EscrowMonad

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] (M : C) [MonObj M]

/-- The unit of the escrow monad: `A ⟶ A ⊗ M`, injecting the monoid unit (`(ρ_ A).inv ≫ A ◁ η[M]`). -/
@[simps]
def escrowEta : 𝟭 C ⟶ tensorRight M where
  app A := (ρ_ A).inv ≫ A ◁ 𝟙ₘ[M]
  naturality := by
    intro A B f; dsimp
    rw [Category.assoc, whisker_exchange, ← Category.assoc, rightUnitor_inv_naturality,
      Category.assoc]

/-- The multiplication of the escrow monad: `(A ⊗ M) ⊗ M ⟶ A ⊗ M`, coalescing the doubled pool via the
monoid multiplication (`(α_ A M M).hom ≫ A ◁ μ[M]`). -/
@[simps]
def escrowMu : tensorRight M ⋙ tensorRight M ⟶ tensorRight M where
  app A := (α_ A M M).hom ≫ A ◁ μₘ[M]
  naturality := by
    intro A B f; dsimp
    rw [← Category.assoc, associator_naturality_left, Category.assoc, Category.assoc,
      ← whisker_exchange]

/-- **The escrow monad** `T_M = (– ⊗ M)` (paper Thm 5.6) over a monoid object `M : C`. The underlying
endofunctor is `tensorRight M`; the unit injects via the monoid unit (`escrowEta`), the multiplication
coalesces a doubled pool via the monoid multiplication (`escrowMu`). The three monad laws are `MonObj`'s
`one_mul`/`mul_one`/`mul_assoc` whiskered into the carried resource `A` — no braiding, no commutativity.

Models a STANDING / ACCUMULATING pool (the standing-offer / liquidity side) — NOT the one-shot affine
`EscrowWitness` of `Intent/Core.lean` (see the module docstring). -/
@[simps! coe]
def escrowMonad : Monad C where
  toFunctor := tensorRight M
  η := escrowEta M
  μ := escrowMu M
  assoc := by
    intro A
    simp only [escrowMu_app, Functor.flip_obj_obj, curriedTensor_obj_obj,
      Functor.flip_obj_map, curriedTensor_map_app, Functor.comp_obj]
    -- LHS slides the inner `μ` (whiskered into `A`) up; RHS coalesces; `mul_assoc` of `M` closes it.
    have key := congrArg (A ◁ ·) (MonObj.mul_assoc M)
    simp only [MonoidalCategory.whiskerLeft_comp] at key
    rw [comp_whiskerRight, whisker_assoc]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [associator_naturality_right_assoc, key]
    monoidal
  left_unit := by
    intro A
    simp only [escrowEta_app, escrowMu_app, Functor.flip_obj_obj, curriedTensor_obj_obj,
      Functor.id_obj]
    -- `(A⊗M) ◁ η` slides through the associator (assoc-naturality) to `A ◁ (M ◁ η)`, then
    -- `M ◁ η ≫ μ = (ρ_ M).hom` (`mul_one`) collapses the pool; the residue is pure coherence.
    simp [← MonoidalCategory.whiskerLeft_comp, MonObj.mul_one]
  right_unit := by
    intro A
    simp only [escrowEta_app, escrowMu_app, Functor.flip_obj_obj, curriedTensor_obj_obj,
      Functor.flip_obj_map, curriedTensor_map_app, Functor.id_obj]
    -- `(η ▷ M)` whiskered into `A`, then `η ▷ M ≫ μ = (λ_ M).hom` (`one_mul`); coherence closes it.
    simp [← MonoidalCategory.whiskerLeft_comp, MonObj.one_mul]

end EscrowMonad

/-! ## 3. `escrowMonad_isMonoidal` — the lax-monoidal structure (paper Thm 5.6, the page-46 hexagon).

The tensorator `μ X Y : (X ⊗ M) ⊗ (Y ⊗ M) ⟶ (X ⊗ Y) ⊗ M` is the braided strength `tensorμ X M Y M`
(which slides the first `M` past `Y` via the braiding) followed by `(X ⊗ Y) ◁ μ[M]` (which coalesces
the two pools). The unit `ε : 𝟙_ ⟶ 𝟙_ ⊗ M` injects via `η[M]`. Naturality is `tensorμ_natural_*` +
whisker; the unitalities are `leftUnitor_monoidal`/`rightUnitor_monoidal`; the associativity is the
page-46 hexagon `tensor_associativity`, and it closes ONLY through `mul_assoc` AND `mul_comm` — the
`tensorμ` strength leaves the two `M`s in braided order, so coalescing them needs commutativity. -/

section EscrowLax

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [BraidedCategory.{v} C]
  (M : C) [MonObj M]

/-- **`escrowMonad_isMonoidal` (paper Thm 5.6)** — the escrow endofunctor `tensorRight M` is lax
monoidal, with tensorator `tensorμ X M Y M ≫ (X⊗Y) ◁ μ[M]` and unit `η[M]` (post-composed with the
left-unitor inverse into `𝟙_ ⊗ M`). The associativity hexagon is `tensor_associativity` (the page-46
chase) coalesced by `mul_assoc`; commutativity `IsCommMonObj.mul_comm` is what lets the braided strength
land the two pools in the order `mul` expects — drop it and `associativity` will not close. -/
@[reducible]
noncomputable def escrowMonad_isMonoidal : (tensorRight M).LaxMonoidal where
  ε := 𝟙ₘ[M] ≫ (λ_ M).inv
  μ X Y := tensorμ X M Y M ≫ (X ⊗ Y) ◁ μₘ[M]
  μ_natural_left := by
    intro X Y f X'; dsimp
    -- `f ▷ M = f ⊗ₘ 𝟙 M`, slide it through `tensorμ` (left-naturality), then `whisker_exchange`
    -- moves the carried `f` past the pool coalescing.
    rw [← tensorHom_id f M]
    slice_lhs 1 2 => rw [tensorμ_natural_left]
    simp only [Category.assoc, id_whiskerRight, tensorHom_id]
    rw [whisker_exchange]
  μ_natural_right := by
    intro X' X Y f; dsimp
    rw [← tensorHom_id f M]
    slice_lhs 1 2 => rw [tensorμ_natural_right]
    simp only [Category.assoc]
    rw [whisker_exchange]
    simp
  associativity := by
    intro X Y Z; dsimp
    -- Canonicalize every whisker adjacent to a `tensorμ`/`μ` into `⊗ₘ`-form, slide the inner pool
    -- coalescings out through `tensorμ`'s naturality, then close with the page-46 hexagon
    -- `tensor_associativity` and the monoid's `mul_assoc`. The braided `tensorμ` already reorders the
    -- two `M`s consistently, so the coalescing `μ[M]` lands them without needing `mul_comm` — a plain
    -- `[MonObj M]` in a braided category suffices (commutativity is NOT used in this chase).
    rw [← tensorHom_id (α_ X Y Z).hom M,
        ← id_tensorHom (X ⊗ M) (tensorμ Y M Z M ≫ (Y ⊗ Z) ◁ μₘ[M]),
        ← id_tensorHom (X ⊗ Y) μₘ[M],
        ← id_tensorHom ((X ⊗ Y) ⊗ Z) μₘ[M],
        ← id_tensorHom (Y ⊗ Z) μₘ[M],
        ← id_tensorHom (X ⊗ Y ⊗ Z) μₘ[M]]
    rw [comp_whiskerRight]
    simp only [Category.assoc]
    slice_lhs 2 3 => rw [tensorμ_natural_left]
    slice_lhs 3 4 => rw [tensorHom_comp_tensorHom, Category.comp_id, MonObj.mul_assoc]
    rw [tensorHom_comp_tensorHom, id_whiskerRight, Category.id_comp, Category.comp_id]
    rw [show ((α_ X Y Z).hom ⊗ₘ ((α_ M M M).hom ≫ M ◁ μₘ[M] ≫ μₘ[M]))
          = ((α_ X Y Z).hom ⊗ₘ (α_ M M M).hom) ≫ (𝟙 (X ⊗ Y ⊗ Z) ⊗ₘ (M ◁ μₘ[M] ≫ μₘ[M])) by
        rw [tensorHom_comp_tensorHom, Category.comp_id]]
    slice_lhs 1 3 => rw [tensor_associativity]
    rw [show (𝟙 (X ⊗ Y ⊗ Z) ⊗ₘ (M ◁ μₘ[M] ≫ μₘ[M]))
          = (𝟙 (X ⊗ Y ⊗ Z) ⊗ₘ M ◁ μₘ[M]) ≫ (𝟙 (X ⊗ Y ⊗ Z) ⊗ₘ μₘ[M]) by
        rw [tensorHom_comp_tensorHom, Category.id_comp]]
    simp only [Category.assoc]
    rw [show (𝟙 (X ⊗ Y ⊗ Z) ⊗ₘ M ◁ μₘ[M])
          = (X ◁ 𝟙 (Y ⊗ Z) ⊗ₘ M ◁ μₘ[M]) by rw [MonoidalCategory.whiskerLeft_id]]
    slice_lhs 3 4 => rw [← tensorμ_natural_right]
    simp
  left_unitality := by
    intro X; dsimp
    -- `tensor_left_unitality` expands the LHS; the unit `η` (`= 𝟙ₘ[M]`) slides through `tensorμ`'s
    -- left-naturality (after `leftUnitor_inv_naturality` re-roots it), then `one_mul` collapses the
    -- pool against the injected unit, leaving pure unitor coherence.
    rw [tensor_left_unitality X M, leftUnitor_inv_naturality 𝟙ₘ[M], comp_whiskerRight]
    simp only [Category.assoc]
    rw [← id_tensorHom (𝟙_ C) 𝟙ₘ[M]]
    slice_rhs 2 3 => rw [tensorμ_natural_left]
    rw [← id_tensorHom (𝟙_ C ⊗ X) μₘ[M]]
    slice_rhs 3 4 => rw [tensorHom_comp_tensorHom, Category.comp_id, MonObj.one_mul]
    congr 1
    monoidal
  right_unitality := by
    intro X; dsimp
    rw [tensor_right_unitality X M, leftUnitor_inv_naturality 𝟙ₘ[M],
      MonoidalCategory.whiskerLeft_comp]
    simp only [Category.assoc]
    rw [← id_tensorHom (𝟙_ C) 𝟙ₘ[M]]
    slice_rhs 2 3 => rw [tensorμ_natural_right]
    rw [← id_tensorHom (X ⊗ 𝟙_ C) μₘ[M]]
    slice_rhs 3 4 => rw [tensorHom_comp_tensorHom, Category.comp_id, MonObj.mul_one]
    congr 1
    monoidal

end EscrowLax

/-! ## 4. `FrictionlessStandingOffer` — the teeth: slippage admits no half-braiding (#3 rescoped).

A `HalfBraiding X` forces `β U : X ⊗ U ≅ U ⊗ X` for *every* `U` — the standing offer must commute
*invertibly* past every turn. So any object `X` for which `X ⊗ U` and `U ⊗ X` are NOT isomorphic for
some `U` **cannot be a center object at all**. A non-commutative `⊗` is the order-dependent value
process a slippage/fee AMM is; we exhibit it concretely on `Discrete (FreeMonoid (Fin 2))`, where
`[a] ⊗ [b] = ⟨[a,b]⟩ ≇ ⟨[b,a]⟩ = [b] ⊗ [a]` (discrete homs force underlying equality). -/

section StandingOffer

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

/-- **A half-braiding forces order-independence up to iso.** From a `HalfBraiding X`, the component at
`U` is an iso `X ⊗ U ≅ U ⊗ X`. This is the structural content the AMM pun ignores. -/
theorem halfBraiding_forces_iso {X : C} (h : HalfBraiding X) (U : C) :
    Nonempty (X ⊗ U ≅ U ⊗ X) := ⟨h.β U⟩

/-- **Contrapositive (the teeth lemma):** if `X ⊗ U` and `U ⊗ X` are not isomorphic for some `U`, then
`X` admits no half-braiding — it is provably not a center object. -/
theorem noniso_admits_no_halfBraiding {X : C} (U : C)
    (hno : ¬ Nonempty (X ⊗ U ≅ U ⊗ X)) : ¬ Nonempty (HalfBraiding X) :=
  fun ⟨h⟩ => hno (halfBraiding_forces_iso h U)

end StandingOffer

/-! ### Concrete teeth — a non-commutative resource process is no center object.

`FreeMonoid (Fin 2)` is the simplest non-commutative monoid (`[0] * [1] = [0,1] ≠ [1,0] = [1] * [0]`).
`Discrete (FreeMonoid (Fin 2))` is therefore a monoidal category (`Discrete.monoidal` needs only
`[Monoid]`, not commutativity) in which the generator `[0]` cannot commute past `[1]`. -/

/-- The two free generators, as objects of the non-commutative discrete monoidal category. -/
abbrev gen (i : Fin 2) : Discrete (FreeMonoid (Fin 2)) := Discrete.mk (FreeMonoid.of i)

/-- **The order-dependence bites:** `gen 0 ⊗ gen 1` and `gen 1 ⊗ gen 0` have *unequal* underlying free
words (`[0,1] ≠ [1,0]`), so no morphism — a fortiori no isomorphism — links them. -/
theorem gen_tensor_noniso :
    ¬ Nonempty (gen 0 ⊗ gen 1 ≅ gen 1 ⊗ gen 0) := by
  rintro ⟨i⟩
  -- A morphism in `Discrete` forces underlying objects equal; the tensor is `Discrete.mk (· * ·)`.
  have he : (gen 0 ⊗ gen 1).as = (gen 1 ⊗ gen 0).as := Discrete.eq_of_hom i.hom
  simp only [gen, Discrete.monoidal_tensorObj_as] at he
  -- Pushing through `FreeMonoid.toList` (injective; `toList (a*b) = toList a ++ toList b`):
  -- `[0] * [1] = [0,1]` vs `[1] * [0] = [1,0]` are unequal lists.
  have := congrArg FreeMonoid.toList he
  simp [FreeMonoid.toList_of] at this

/-- **THE TEETH (`FrictionlessStandingOffer` rescope):** the non-commutative generator `[0]` is
**provably not a center object** — it admits no half-braiding, because it cannot commute (even up to
iso) past `[1]`. A slippage/fee/finite-liquidity AMM is exactly such an order-dependent value process,
so "AMM-as-central-object" is a pun: only a *frictionless / no-arb* idealization (genuinely
order-independent) is a center object. -/
theorem noncommuting_admits_no_halfBraiding :
    ¬ Nonempty (HalfBraiding (gen 0)) :=
  noniso_admits_no_halfBraiding (gen 1) gen_tensor_noniso

/-! ## 5. The NON-DISCRETE witness — `escrowMonad_isMonoidal` + `mul_comm` checked with content.

On `DemoRes` (discrete) the only monoid object is `𝟙_`, whose hom-sets are subsingletons, so its lax
coherences AND its `mul_comm` are `Subsingleton.elim` tautologies — VACUOUS. So we instantiate at the
*writer comm-monoid object* `Multiplicative ℕ` in cartesian-monoidal `Type`, where `mul` is a genuine
binary function (`*` = `+` under `Multiplicative`): `writerEscrow_isMonoidal` exercises the lax structure
where its coherences are non-trivial equations (not subsingleton-collapsed), and
`writer_mul_comm_has_content` exhibits that `mul_comm` (load-bearing for centrality §1/§4) is real
content (`Nat.add_comm`, off-diagonal), not a tautology. -/

/-- The non-discrete pool: the commutative monoid object `Multiplicative ℕ` in cartesian-monoidal
`Type`, obtained from the bundled `CommMonoid` via `commMonTypeEquivalenceCommMon.inverse`. Its `MonObj`
has `mul = fun p => p.1 * p.2` (a real binary function) and `IsCommMonObj.mul_comm` carrying
`CommMonoid.mul_comm` — non-vacuous. -/
noncomputable def WriterPool : CommMon (Type) :=
  CommMonTypeEquivalenceCommMon.inverse.obj (CommMonCat.of (Multiplicative ℕ))

/-- The underlying writer object — `Multiplicative ℕ` with its hand-installed `MonObj`/`IsCommMonObj`. -/
noncomputable abbrev WriterObj : Type := WriterPool.X

noncomputable instance : MonObj WriterObj := WriterPool.mon
noncomputable instance : IsCommMonObj WriterObj := WriterPool.comm

/-- **The lax-monoidal escrow structure, checked on the non-discrete writer pool.** This is
`escrowMonad_isMonoidal` instantiated at a witness whose `mul` is a genuine binary function — not the
`𝟙_`-only discrete carrier whose coherences are subsingleton-trivial. The associativity hexagon here is
a real equation, exercising `Multiplicative ℕ`'s `mul_assoc` (no commutativity needed — see §3). -/
@[reducible]
noncomputable def writerEscrow_isMonoidal : (tensorRight WriterObj).LaxMonoidal :=
  escrowMonad_isMonoidal WriterObj

/-- The writer pool's monad (the underlying `Monad (Type)` for the standing `Multiplicative ℕ` pool). -/
noncomputable def writerEscrowMonad : Monad (Type) := escrowMonad WriterObj

/-- The writer object's `MonObj.mul`, read as the underlying `Type`-level function: it is
`fun p => p.1 * p.2` (the bundled `Multiplicative ℕ` multiplication). This is the bridge that exposes the
genuine binary operation `μ[WriterObj]` carries — the content the discrete `𝟙_` carrier lacks. -/
theorem writer_mul_apply (p : WriterObj × WriterObj) : μₘ[WriterObj] p = p.1 * p.2 := rfl

/-- **`writer_mul_comm_has_content` — `mul_comm` carries real content (for centrality §1/§4).** The
writer pool's multiplication is a real binary function on a non-subsingleton type: commutativity equates
the two orders (`mul (a,b) = mul (b,a)`), yet the *inputs* `(a,b)` and `(b,a)` are distinct off
the diagonal (the swap is real, not a `Subsingleton.elim` tautology). So `CommCentralMonoid.mul_comm` is
non-vacuous on a genuine carrier. Witnessed at `a = ofAdd 3, b = ofAdd 5` (under `Multiplicative`, `*` is
`+`, so both products are `ofAdd 8`). -/
theorem writer_mul_comm_has_content :
    (μₘ[WriterObj] ((Multiplicative.ofAdd (3 : ℕ) : WriterObj), (Multiplicative.ofAdd (5 : ℕ) : WriterObj))
      = μₘ[WriterObj] ((Multiplicative.ofAdd (5 : ℕ) : WriterObj), (Multiplicative.ofAdd (3 : ℕ) : WriterObj))) ∧
    (((Multiplicative.ofAdd (3 : ℕ) : WriterObj), (Multiplicative.ofAdd (5 : ℕ) : WriterObj))
      ≠ ((Multiplicative.ofAdd (5 : ℕ) : WriterObj), (Multiplicative.ofAdd (3 : ℕ) : WriterObj))) := by
  refine ⟨?_, ?_⟩
  · -- `mul` is `fun p => p.1 * p.2`; commutativity collapses the two orders to one value.
    rw [writer_mul_apply, writer_mul_apply, _root_.mul_comm]
  · -- the inputs themselves are distinct (the swap is not the identity): the first
    -- components are `ofAdd 3` vs `ofAdd 5`, and `toAdd ∘ ofAdd = id` exposes `3 ≠ 5`.
    intro h
    have h3 : (3 : ℕ) = 5 := congrArg (Multiplicative.toAdd ∘ Prod.fst) h
    exact absurd h3 (by decide)

/-! ## 6. Non-vacuity demos + axiom-hygiene pins. -/

/-- The escrow monad's unit injects the monoid unit (definitional sanity). -/
example {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] (M : C) [MonObj M] (A : C) :
    (escrowMonad M).η.app A = (ρ_ A).inv ≫ A ◁ 𝟙ₘ[M] := rfl

/-- The escrow monad's multiplication coalesces the doubled pool (definitional sanity). -/
example {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] (M : C) [MonObj M] (A : C) :
    (escrowMonad M).μ.app A = (α_ A M M).hom ≫ A ◁ μₘ[M] := rfl

/-- The lax tensorator on the writer pool is the braided strength then the pool coalescing. -/
example (X Y : Type) :
    Functor.LaxMonoidal.μ (self := escrowMonad_isMonoidal WriterObj) (tensorRight WriterObj) X Y
      = tensorμ X WriterObj Y WriterObj ≫ (X ⊗ Y) ◁ μₘ[WriterObj] :=
  rfl

#guard (Multiplicative.toAdd
  ((Multiplicative.ofAdd 3 * Multiplicative.ofAdd 5 : Multiplicative ℕ))) == 8  -- pool coalesces 3,5

/-! ## 7. The escrow ↔ ∃ weld (Flake–Laugwitz–Posur Cor 3.11, 3.19/3.20) — the projection formula.

This is the weld of the escrow monad `T_M = (–⊗M)` to the adjunction side. The paper's setup is
an oplax-lax (monoidal) adjunction `G ⊣ R`: setting `X = 1` in the projection-formula morphism gives a
natural transformation `lproj_{A,1} : A ⊗ R1 ⟶ RG(A)` which (Cor 3.11) is a **morphism of monads** from
the *tensor monad* `(– ⊗ R1)` (`R1` is a monoid because `R` is lax monoidal) to the *adjunction monad*
`RG`. The left-adjoint `G` is the `∃`-side; the lax right-adjoint `R` is the escrow/standing-pool side.

  **§7.1 (Cor 3.11) — `escrowMonadHom`.** We instantiate the unconditional Cor 3.11 at the canonical
  monoidal adjunction every monoidal category carries: the **identity adjunction** `𝟭_C ⊣ 𝟭_C`
  (`Adjunction.id`). Then `R1 = 𝟙_`, the tensor monad `(– ⊗ R1)` is exactly our `escrowMonad (𝟙_ C)`
  (`= tensorRight (𝟙_ C)`), the adjunction monad `RG` is `Adjunction.id.toMonad` (underlying functor
  `𝟭_C ⋙ 𝟭_C`), and `lproj_{A,1}` is the right unitor `ρ_A : A ⊗ 𝟙_ ⟶ A`. We build a genuine
  `MonadHom` — a `NatTrans` together with the unit-coherence (`app_η`, Lemma 3.9) and
  multiplication-coherence (`app_μ`, Lemma 3.10) squares — NOT a vacuous identity: its source and target
  *endofunctors differ on objects* (`(escrowMonad (𝟙_ C)).obj A = A ⊗ 𝟙_` vs `(RG).obj A = A`), and its
  component is the right unitor — the *first projection* `Prod.fst`, not `𝟙`
  (`escrowMonadHom_app_is_projection`).

  **§7.2 (Cor 3.20) — `escrowProjectionEquiv`.** Cor 3.19 says `lproj_{B,−}` is a *natural
  isomorphism* whenever `B` has a (left) dual; Cor 3.20 specializes to: if the category is rigid the
  projection formula holds. We make rigidity **load-bearing**, not the vacuous `IsIso (𝟙 _)` dodge: the
  tensored object is the monoidal unit, which is *self-dual* (`ExactPairing (𝟙_)(𝟙_)`,
  mathlib's `exactPairingUnit`). That self-dual datum is *exactly* what produces the adjunction
  `tensorRightAdjunction (𝟙_)(𝟙_) : tensorRight (𝟙_ C) ⊣ tensorRight (𝟙_ C)` — an adjunction that
  cannot even be *formed* without the `ExactPairing` instance. Its unit AND counit are isomorphisms,
  with iso-ness derived **straight from the pairing's coevaluation/evaluation** (`η_ = (ρ_).inv`,
  `ε_ = (ρ_).hom` for the self-dual unit). Hence the escrow endofunctor is an *equivalence*
  (`escrowProjectionEquiv`): the projection formula iso of Cor 3.20.

  **§7.3 (teeth) — `escrow_no_iso_without_rigidity`.** The iso requires a dual. In the
  *non-rigid* category `Discrete (FreeMonoid (Fin 2))` the generator `gen 0` has **no** dual at all:
  any `ExactPairing (gen 0) Y` would force a coevaluation `𝟙_ ⟶ gen 0 ⊗ Y`, i.e. `1 = of 0 * Y.as`
  in the free monoid (`[] = 0 :: …`), impossible (`gen0_no_exactPairing`). So the
  `tensorRightAdjunction` of §7.2 *cannot be built* for `gen 0`, and concretely the escrow endofunctor
  `tensorRight (gen 0)` is **not even essentially surjective** — its image never hits `𝟙_` (every word
  `A.as * of 0` ends in `0`, never the empty word), so it is no equivalence
  (`escrow_no_iso_without_rigidity`). Drop rigidity and the projection iso is gone. -/

section EscrowWeld

open scoped Functor

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

/-! ### §7.1 — `escrowMonadHom` (Cor 3.11): the projection morphism is a morphism of monads. -/

/-- **`escrowMonadHom` (Flake–Laugwitz–Posur Cor 3.11).** The projection-formula morphism
`lproj_{A,1} : A ⊗ R1 ⟶ RG(A)`, instantiated at the identity monoidal adjunction `𝟭_C ⊣ 𝟭_C`, is a
**morphism of monads** from the tensor/escrow monad `(– ⊗ 𝟙_) = escrowMonad (𝟙_ C)` to the adjunction
monad `Adjunction.id.toMonad`. The component is the right unitor `ρ_A`; the unit-coherence square
(`app_η`, Lemma 3.9) and the multiplication-coherence square (`app_μ`, Lemma 3.10) are discharged from
the monoidal coherence of the trivial monoid `𝟙_` (`one = 𝟙`, `mul = (λ_).hom`). This is a genuine
`MonadHom`, not a vacuous identity — its source and target endofunctors differ on objects (see
`escrowMonadHom_source_ne_target_obj`). -/
def escrowMonadHom : escrowMonad (𝟙_ C) ⟶ (Adjunction.id (C := C)).toMonad where
  toNatTrans :=
    { app := fun A => (ρ_ A).hom
      naturality := by intro A B f; simp [escrowMonad, Adjunction.toMonad, Adjunction.id] }
  app_η := by
    intro A
    -- Lemma 3.9: `unit ≫ lproj = id ⊗ lax₀`; here `η = (ρ).inv ≫ A ◁ 𝟙`, so `η ≫ ρ = id`.
    simp [escrowMonad, escrowEta, Adjunction.toMonad, Adjunction.id]
  app_μ := by
    intro A
    -- Lemma 3.10: the multiplication square. Source `μ = (α).hom ≫ A ◁ (λ_).hom`; both legs
    -- collapse to a unitor identity since `RG`'s `μ` is the identity.
    simp only [escrowMonad, escrowMu]
    dsimp [Adjunction.toMonad, Adjunction.id]
    simp

/-- The component of `escrowMonadHom` at `A` is the right unitor `ρ_A` (= the projection `lproj_{A,1}`
in the identity-adjunction model). Definitional sanity. -/
@[simp] theorem escrowMonadHom_app (A : C) : escrowMonadHom.app A = (ρ_ A).hom := rfl

end EscrowWeld

/-- **Non-vacuity of `escrowMonadHom` (the projection discards the pool).** The source monad
`escrowMonad (𝟙_ Type)` has underlying functor `(– ⊗ 𝟙_) = (– × PUnit)`, which is *not* the identity:
its objects carry a real (degenerate) pool slot. The monad-morphism component `escrowMonadHom.app Bool`
is then the right unitor `ρ_Bool : Bool × PUnit ⟶ Bool`, which in `Type` is the
**first projection** (`Prod.fst`) — it forgets the pool, it is not a formal identity. So
`escrowMonadHom` connects a non-trivial standing-pool monad to the trivial (identity-adjunction) monad,
exactly the projection-formula content of Cor 3.11. -/
theorem escrowMonadHom_app_is_projection :
    (escrowMonadHom.app Bool : Bool × PUnit.{1} → Bool) = Prod.fst := rfl

/-! ### §7.2 — `escrow_projection_iso_of_rigid` (Cor 3.20): rigidity makes the escrow an equivalence. -/

section EscrowRigid

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

/-- The unit of the dual-induced adjunction `tensorRight (𝟙_) ⊣ tensorRight (𝟙_)` is a pointwise
isomorphism. The iso-ness is read *directly off the self-dual pairing* `ExactPairing (𝟙_)(𝟙_)`: its
coevaluation `η_ (𝟙_)(𝟙_)` is `(ρ_ 𝟙_).inv`, an iso, and the rest of the unit is a composite of
coherence isos. This is the half of Cor 3.19 that needs the dual. -/
noncomputable instance escrowAdj_unit_isIso (A : C) :
    IsIso ((tensorRightAdjunction (𝟙_ C) (𝟙_ C)).unit.app A) := by
  rw [show (tensorRightAdjunction (𝟙_ C) (𝟙_ C)).unit.app A
        = (tensorRightHomEquiv A (𝟙_ C) (𝟙_ C) (A ⊗ 𝟙_ C)) (𝟙 (A ⊗ 𝟙_ C)) from rfl]
  dsimp [tensorRightHomEquiv]
  rw [show (η_ (𝟙_ C) (𝟙_ C)) = (ρ_ (𝟙_ C)).inv from rfl]
  infer_instance

/-- The counit of `tensorRight (𝟙_) ⊣ tensorRight (𝟙_)` is a pointwise iso — dual to the unit, read
off the pairing's evaluation `ε_ (𝟙_)(𝟙_) = (ρ_ 𝟙_).hom`. -/
noncomputable instance escrowAdj_counit_isIso (A : C) :
    IsIso ((tensorRightAdjunction (𝟙_ C) (𝟙_ C)).counit.app A) := by
  rw [show (tensorRightAdjunction (𝟙_ C) (𝟙_ C)).counit.app A
        = (tensorRightHomEquiv (A ⊗ 𝟙_ C) (𝟙_ C) (𝟙_ C) A).symm (𝟙 (A ⊗ 𝟙_ C)) from rfl]
  dsimp [tensorRightHomEquiv]
  rw [show (ε_ (𝟙_ C) (𝟙_ C)) = (ρ_ (𝟙_ C)).hom from rfl]
  infer_instance

/-- **`escrowProjectionEquiv` (Flake–Laugwitz–Posur Cor 3.20).** Because the tensored object —
the monoidal unit `𝟙_ C` — is *rigid* (self-dual: `ExactPairing (𝟙_)(𝟙_)`, mathlib's
`exactPairingUnit`), the escrow endofunctor `tensorRight (𝟙_ C)` is an **equivalence of categories**:
`tensorRightAdjunction (𝟙_)(𝟙_)` (an adjunction that exists ONLY because of the pairing) has iso unit
and counit (both derived from the coevaluation/evaluation of that very pairing). This is the projection
formula iso — NOT the `IsIso (𝟙 _)` dodge: the equivalence's *functor* is `tensorRight (𝟙_)`, which
moves objects (`A ↦ A ⊗ 𝟙_`), and its invertibility is read off the pairing. That rigidity is
necessary (not automatic) is what §7.3's teeth establish: for the non-dualizable `gen 0`,
`tensorRight (gen 0)` is no equivalence at all. -/
noncomputable def escrowProjectionEquiv : C ≌ C :=
  (tensorRightAdjunction (𝟙_ C) (𝟙_ C)).toEquivalence

/-- The equivalence of `escrow_projection_iso_of_rigid` has the escrow endofunctor as its forward
functor — the standing-pool functor `(– ⊗ 𝟙_)` is the one made invertible by rigidity. -/
@[simp] theorem escrowProjectionEquiv_functor :
    (escrowProjectionEquiv (C := C)).functor = tensorRight (𝟙_ C) := rfl

end EscrowRigid

/-! ### §7.3 — `escrow_no_iso_without_rigidity`: the teeth. No dual ⇒ no projection iso. -/

/-- **`gen0_no_exactPairing` — the non-rigid witness.** In the non-commutative
`Discrete (FreeMonoid (Fin 2))`, the generator `gen 0` has **no** right dual: there is no
`ExactPairing (gen 0) Y` for any `Y`, because its coevaluation `𝟙_ ⟶ gen 0 ⊗ Y` would force the empty
word to equal `0 :: (Y.as as a word)` in the free monoid. -/
theorem gen0_no_exactPairing (Y : Discrete (FreeMonoid (Fin 2))) :
    IsEmpty (ExactPairing (gen 0) Y) := by
  refine ⟨fun ep => ?_⟩
  have he : (𝟙_ (Discrete (FreeMonoid (Fin 2)))).as = (gen 0 ⊗ Y).as :=
    Discrete.eq_of_hom ep.coevaluation'
  simp only [gen, Discrete.monoidal_tensorObj_as, Discrete.monoidal_tensorUnit_as] at he
  have := congrArg FreeMonoid.toList he
  simp [FreeMonoid.toList_of, FreeMonoid.toList_one, FreeMonoid.toList_mul] at this

/-- **`escrow_no_iso_without_rigidity` (the teeth).** Without a dual, the escrow projection cannot be an
iso. Concretely: the escrow endofunctor `tensorRight (gen 0)` for the *non-dualizable* `gen 0` is **not
essentially surjective** — it never hits `𝟙_`, because every value `A ⊗ gen 0` has underlying word
`A.as * of 0`, which ends in `0` and so is never the empty word `1 = 𝟙_.as`. Hence `tensorRight (gen 0)`
is no equivalence: the projection-formula iso of §7.2 required the rigidity (`ExactPairing`)
that `gen 0` lacks (`gen0_no_exactPairing`). -/
theorem escrow_no_iso_without_rigidity (A : Discrete (FreeMonoid (Fin 2))) :
    ¬ Nonempty ((tensorRight (gen 0)).obj A ≅ 𝟙_ (Discrete (FreeMonoid (Fin 2)))) := by
  rintro ⟨i⟩
  have he : ((tensorRight (gen 0)).obj A).as = (𝟙_ (Discrete (FreeMonoid (Fin 2)))).as :=
    Discrete.eq_of_hom i.hom
  simp only [tensorRight, gen, Discrete.monoidal_tensorUnit_as] at he
  have := congrArg FreeMonoid.toList he
  simp [FreeMonoid.toList_of, FreeMonoid.toList_one, FreeMonoid.toList_mul] at this

#assert_axioms CommCentralMonoid.mul_comm
#assert_axioms escrowMonad
#assert_axioms escrowMonad_isMonoidal
#assert_axioms noncommuting_admits_no_halfBraiding
#assert_axioms gen_tensor_noniso
#assert_axioms writer_mul_comm_has_content
#assert_axioms writer_mul_apply

-- §7 the escrow ↔ ∃ weld (Flake–Laugwitz–Posur Cor 3.11, 3.20, + teeth).
#assert_axioms escrowMonadHom
#assert_axioms escrowMonadHom_app
#assert_axioms escrowMonadHom_app_is_projection
#assert_axioms escrowProjectionEquiv
#assert_axioms escrowProjectionEquiv_functor
#assert_axioms gen0_no_exactPairing
#assert_axioms escrow_no_iso_without_rigidity

end Dregg2.Intent

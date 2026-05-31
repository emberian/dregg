/-
# Dregg2.Core — the symmetric-monoidal category of cells & turns, plus conservation.

Law 1 (Conservation) is the linear/symmetric-monoidal structure on the category
whose **objects are cells** and whose **morphisms are turns**. The load-bearing
content of conservation `Σ_k` is a **monoid-homomorphism on counts +
invariance on ordinary turns**: `Σ_k (A ⊗ B) = Σ_k A + Σ_k B` (additive across
the monoidal product) and `Σ_k A = Σ_k B` for every `ordinary` turn `A ⟶ B` —
i.e. an honest turn neither creates nor destroys units of resource `k`; it can
only move, withhold (copy `Δ`), or erase (`◇`) them. (The "strong monoidal
functor" packaging is *decorative* — its target is discrete on objects, so the
functor laws collapse to the monoid-hom + invariance; per `dregg2.md §2.1` /
`00-synthesis.md §1`, treat the monoid-hom + invariance as the real obligation.)

Mint/burn are the *only* generators allowed to change `Σ_k`; they are modelled as
explicit typed generators, so conservation is an equality (`=`), never a monotone
bound (`≥`).

Design note: "spec-first, grind up." Law 1's per-turn balance is the one obligation the
in-module data cannot derive; it is carried as the **typeclass field** `ConservesStep cons`
(the `CryptoKernel`/`World` Prop-portal idiom — an explicit, auto-resolved assumption, NOT a
`sorry`), and DISCHARGED for the executable machine in `Exec.StepComplete` (the PROVED
`conservation_step_realized`). The three case-corollaries are then proved from the field. The
boundary law (a different, candidate-dependent module) lands LAST.
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Nat.Defs

namespace Dregg2.Core

open CategoryTheory MonoidalCategory

universe u

/-- A resource kind (e.g. a token/asset class). Conservation is stated per-kind. -/
abbrev ResourceKind := Type u

/- **The value object of conservation is ANY commutative monoid `(M, +, 0)` — not
`ℕ`.** This is forced, not chosen: the *symmetric* (braided) monoidal structure on
cells makes `Σ` land in a **commutative** monoid (`Σ A + Σ B = Σ B + Σ A` from the
symmetry iso), and additivity across `⊗` + a unit is exactly the monoid structure.
`ℕ` is merely the FREE/simplest instance (one fungible asset, no debt). Richer
resources just instantiate `M`:
  * multi-asset      `M = K → ℕ`        — a vector of per-kind counts (subsumes the
                                          old `(k : Nat)` index — kinds are now a
                                          dimension of `M`, not an outer parameter);
  * fractional/contin `M = ℚ≥0 / ℝ≥0`   — divisible shares;
  * debt/credit       `M = ℤ`           — signed balances (an `AddCommGroup`);
  * **partial / linear** (NFTs, fractional permissions, authoritative↔fragment,
    capabilities) — these need composition that can be *invalid*, which a monoid
    cannot express → the **resource-algebra (camera) tier**, see `Resource.lean`. -/
variable {M : Type u} [AddCommMonoid M]

/-- The object type of the cell category: a *cell* is a unit of sovereign state. -/
structure Cell where
  /-- Opaque identity of the cell (data-model value hash in the real system). -/
  id : Nat
  deriving DecidableEq, Repr

/-- Turns split into resource-preserving turns and the two privileged generators.
Only `mint`/`burn` are permitted to move `Σ_k`. -/
inductive TurnTag where
  | ordinary
  | mint (k : Nat) (amount : Nat)
  | burn (k : Nat) (amount : Nat)
  deriving Repr, DecidableEq

/-- The morphism type: a *turn* from one cell-configuration to another.

A turn is the atomic unit of state change. Composition is sequencing of turns;
the monoidal product `⊗` is the independent (concurrent, non-interfering)
juxtaposition of cells/turns. -/
structure Turn (A B : Cell) where
  /-- Tag distinguishing ordinary turns from the mint/burn generators below. -/
  tag : TurnTag
  deriving Repr

/-- The symmetric-monoidal category of cells and turns.

`TODO`: provide the actual `Category`/`MonoidalCategory`/`SymmetricCategory`
instances. Stated as an existence obligation to be discharged first. -/
class TurnCat where
  cat        : Category.{u} Cell
  monoidal   : MonoidalCategory Cell
  symmetric  : SymmetricCategory Cell

/-- **`Σ` : conservation as a monoid-valued measure** `count : Cell → M`, with a per-
generator **inflow** `minted` and **outflow** `burned` (both `: TurnTag → M`). The law is
a BALANCE — `count A + minted = count B + burned` — NOT a single signed delta, because a
bare `AddCommMonoid` has no negation: "burning decreases the count" is unstatable as
`count B = count A + δ` (there is no negative `δ`); it must be the inflow/outflow balance.
(In a group `M` the two collapse to one signed `val`; the balance form is the honest law
for the general monoid.) The load-bearing content is the monoid-hom + invariance; the
"strong monoidal functor" packaging is decorative. -/
structure Conservation (M : Type u) [AddCommMonoid M] where
  /-- Resource measure carried by a cell, valued in the commutative monoid `M`. -/
  count : Cell → M
  /-- Inflow: units a generator MINTS into existence (`0` for ordinary/burn). -/
  minted : TurnTag → M
  /-- Outflow: units a generator BURNS out of existence (`0` for ordinary/mint). -/
  burned : TurnTag → M
  /-- Ordinary turns mint nothing. -/
  ord_minted : minted TurnTag.ordinary = 0
  /-- Ordinary turns burn nothing — together with `ord_minted` this makes ordinary
  turns exactly conservative. -/
  ord_burned : burned TurnTag.ordinary = 0
  /-- A mint generator only mints (it does not also burn). -/
  mint_pure : ∀ k a, burned (TurnTag.mint k a) = 0
  /-- A burn generator only burns (it does not also mint). -/
  burn_pure : ∀ k a, minted (TurnTag.burn k a) = 0
  /-- The monoidal product `⊗` on cells, at the measure level. This is the measure-level
  *shadow* of `TurnCat`'s `MonoidalCategory.tensorObj` (`⊗`); we carry it as data here so
  the monoid-hom content of conservation can be stated without first discharging the full
  `MonoidalCategory Cell` instance (a separate, larger obligation). -/
  tensor : Cell → Cell → Cell
  /-- The monoidal unit `I` on cells, at the measure level — the measure-level shadow of
  `TurnCat`'s `MonoidalCategory.tensorUnit` (`I`). -/
  unit : Cell
  /-- The measure sends the monoidal unit to `0` (the unit-preservation half of the
  monoid-homomorphism: `count I = 0`). -/
  unit_zero : count unit = 0
  /-- Monoid-hom: the measure is additive across the monoidal product
  (`count (A ⊗ B) = count A + count B`). Together with `unit_zero` this says `count` is a
  monoid homomorphism `(Cell, ⊗, I) → (M, +, 0)` — i.e. conservation IS a monoidal functor
  to the discrete monoid `M` (its functor laws collapse to exactly these two equations).
  See: Coecke–Fritz–Spekkens, *A mathematical theory of resources* (conservation = a
  monoidal functor / monoid-hom on the resource monoid); Selinger, *A survey of graphical
  languages for monoidal categories* (the `⊗`/`I` structure these shadow). -/
  tensor_add : ∀ A B, count (tensor A B) = count A + count B

/-- The new `tensor`/`unit`/`unit_zero`/`tensor_add` fields are satisfiable: the trivial
zero-measure is a `Conservation ℕ` (witnesses that de-hollowing added no unmeetable
obligation). The monoid-hom equations hold by `simp` on the constant-`0` measure. -/
example : Conservation ℕ where
  count  := fun _ => 0
  minted := fun _ => 0
  burned := fun _ => 0
  ord_minted := rfl
  ord_burned := rfl
  mint_pure  := fun _ _ => rfl
  burn_pure  := fun _ _ => rfl
  tensor := fun _ B => B
  unit   := ⟨0⟩
  unit_zero  := rfl
  tensor_add := by simp

/-- **The conservation balance (Law 1) — the operational obligation, now a TYPECLASS field.**
Every turn balances inflow against outflow: `count A + minted tag = count B + burned tag`.

This was the one `sorry` of the abstract `Core` layer: there is no data in
`Conservation`/`Turn` from which the equality follows *in-module* — it is the law the
operational semantics must satisfy. Rather than leave it as a `sorry`-bodied theorem (an
unprovable claim) we make it an **explicit assumption carried as a class field**, exactly the
`CryptoKernel`/`World` Prop-portal idiom: `ConservesStep cons` is "the measure `cons` is
realized by an operational model that conserves every turn". The abstract case-corollaries
below then take `[ConservesStep cons]` (auto-resolved) and are PROVED from the field — no
`sorry` anywhere.

This is NOT a vacuous assumption: the executable kernel DISCHARGES it. The instance is
provided in `Exec.StepComplete` from the PROVED `cexec_attests` /
`conservation_step_realized` — the class field is satisfied by a real proof about the
running machine, never re-`sorry`'d. -/
class ConservesStep (cons : Conservation M) : Prop where
  /-- The Law-1 balance for every turn — the operational model's obligation. -/
  step : ∀ {A B : Cell} (f : Turn A B),
    cons.count A + cons.minted f.tag = cons.count B + cons.burned f.tag

/-- **The conservation balance (Law 1).** Accessor for the `ConservesStep` class field, so
the abstract law reads as a lemma `conservation_step cons f` (the constraint
`[ConservesStep cons]` is implicit, auto-resolved at every call site). Equality, never `≥`. -/
theorem conservation_step
    (cons : Conservation M) [ConservesStep cons]
    {A B : Cell} (f : Turn A B) :
    cons.count A + cons.minted f.tag = cons.count B + cons.burned f.tag :=
  ConservesStep.step f

/-- **Conservation on ordinary turns — PROVED** from `conservation_step`: an `ordinary`
turn preserves the measure exactly (both inflow and outflow collapse to `0`). -/
theorem conservation_ordinary
    (cons : Conservation M) [ConservesStep cons]
    {A B : Cell} (f : Turn A B) (h : f.tag = TurnTag.ordinary) :
    cons.count A = cons.count B := by
  have hs := conservation_step cons f
  rw [h, cons.ord_minted, cons.ord_burned, add_zero, add_zero] at hs
  exact hs

/-- A `mint` generator increases the measure by its inflow — **PROVED** from
`conservation_step` + `mint_pure`. -/
theorem mint_delta
    (cons : Conservation M) [ConservesStep cons] (k amount : Nat)
    {A B : Cell} (f : Turn A B) (h : f.tag = TurnTag.mint k amount) :
    cons.count B = cons.count A + cons.minted (TurnTag.mint k amount) := by
  have hs := conservation_step cons f
  rw [h, cons.mint_pure, add_zero] at hs
  exact hs.symm

/-- A `burn` generator decreases the measure by its outflow, stated **additively**
(`count A = count B + outflow`, no truncated subtraction) — **PROVED** from
`conservation_step` + `burn_pure`. -/
theorem burn_delta
    (cons : Conservation M) [ConservesStep cons] (k amount : Nat)
    {A B : Cell} (f : Turn A B) (h : f.tag = TurnTag.burn k amount) :
    cons.count A = cons.count B + cons.burned (TurnTag.burn k amount) := by
  have hs := conservation_step cons f
  rw [h, cons.burn_pure, add_zero] at hs
  exact hs

/-- **No free copy (the linearity / "withholding" law) — PROVED.** A comonoid copy map
`Δ : A ⟶ A ⊗ A` that is *conservation-respecting* (an `ordinary` turn — one that neither
mints nor burns) would force `count A = count A + count A` (by `conservation_ordinary` into
`tensor A A`, then `tensor_add`). In a **cancellative** commutative monoid that equation
collapses to `count A = 0`: there is NO conserving duplication of a non-empty resource.
This is exactly comonoid coherence as a *conservation* constraint — `Δ` is admissible only
on the zero-measure (empty) cell; copying anything with `count A ≠ 0` is non-conservative
(it must instead mint, which is a privileged generator, not an `ordinary` turn).

The `[AddLeftCancelMonoid M]` hypothesis is the honest extra datum: a bare `AddCommMonoid`
cannot *state* "no free copy" (it has no cancellation, so `x = x + x` need not give `x = 0`
— e.g. in `ℕ∞` with `⊤ = ⊤ + ⊤`); cancellation is exactly the structure that makes a
fungible resource *count* rather than *saturate*. `ℕ` (the canonical resource monoid) is
`AddLeftCancelMonoid`, so the law applies to the real fungible-asset instance. -/
theorem withholding_no_free_copy {M : Type u} [AddCommMonoid M] [IsCancelAdd M]
    (cons : Conservation M) [ConservesStep cons] (A : Cell)
    (copy : Turn A (cons.tensor A A)) (hcopy : copy.tag = TurnTag.ordinary) :
    cons.count A = 0 := by
  -- ordinary copy preserves the measure: count A = count (tensor A A)
  have hpres : cons.count A = cons.count (cons.tensor A A) :=
    conservation_ordinary cons copy hcopy
  -- tensor_add unfolds the target: count (tensor A A) = count A + count A
  rw [cons.tensor_add A A] at hpres
  -- count A = count A + count A  ⟹  count A = 0  by cancellation
  exact left_eq_add.mp hpres

end Dregg2.Core

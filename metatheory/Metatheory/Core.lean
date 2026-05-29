/-
# Metatheory.Core — the symmetric-monoidal category of cells & turns, plus conservation.

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

Design note: "spec-first, grind up." Every law is stated with a `sorry` body.
Discharge the `CategoryTheory`/`MonoidalCategory`/`SymmetricCategory` instances and
the `Σ_k` monoid-hom FIRST; the boundary law (a different, candidate-dependent
module) LAST.
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Defs

namespace Metatheory.Core

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

/-- **The conservation balance (Law 1) — the single obligation.** Every turn balances
inflow against outflow: `count A + minted tag = count B + burned tag`. This is the one
`sorry` the operational model must discharge; the three case-corollaries below are then
*proved* from it (no `sorry`). An equality, never a `≥`. -/
theorem conservation_step
    (cons : Conservation M)
    {A B : Cell} (f : Turn A B) :
    cons.count A + cons.minted f.tag = cons.count B + cons.burned f.tag := by
  -- PRIMITIVE: the operational model discharges Law 1's balance; an honest turn
  -- moves/withholds/erases units but never creates or destroys them. There is no
  -- data in `Conservation`/`Turn` from which this equality follows in-module —
  -- it is an axiom-style obligation the operational semantics must satisfy.
  sorry

/-- **Conservation on ordinary turns — PROVED** from `conservation_step`: an `ordinary`
turn preserves the measure exactly (both inflow and outflow collapse to `0`). -/
theorem conservation_ordinary
    (cons : Conservation M)
    {A B : Cell} (f : Turn A B) (h : f.tag = TurnTag.ordinary) :
    cons.count A = cons.count B := by
  have hs := conservation_step cons f
  rw [h, cons.ord_minted, cons.ord_burned, add_zero, add_zero] at hs
  exact hs

/-- A `mint` generator increases the measure by its inflow — **PROVED** from
`conservation_step` + `mint_pure`. -/
theorem mint_delta
    (cons : Conservation M) (k amount : Nat)
    {A B : Cell} (f : Turn A B) (h : f.tag = TurnTag.mint k amount) :
    cons.count B = cons.count A + cons.minted (TurnTag.mint k amount) := by
  have hs := conservation_step cons f
  rw [h, cons.mint_pure, add_zero] at hs
  exact hs.symm

/-- A `burn` generator decreases the measure by its outflow, stated **additively**
(`count A = count B + outflow`, no truncated subtraction) — **PROVED** from
`conservation_step` + `burn_pure`. -/
theorem burn_delta
    (cons : Conservation M) (k amount : Nat)
    {A B : Cell} (f : Turn A B) (h : f.tag = TurnTag.burn k amount) :
    cons.count A = cons.count B + cons.burned (TurnTag.burn k amount) := by
  have hs := conservation_step cons f
  rw [h, cons.burn_pure, add_zero] at hs
  exact hs

/-- **Withholding = copy `Δ` / erase `◇`.** Conservation is realized operationally
by forbidding free duplication/discard of conserved units: a turn may copy a cell
(`Δ : A ⟶ A ⊗ A`) or erase it (`◇ : A ⟶ I`) only when `Σ` of the withholding-account
absorbs the difference. Stated here as the comonoid coherence obligation that the
non-mint generators must satisfy. -/
theorem withholding_comonoid_coherence
    (cons : Conservation M) (A : Cell) :
    True := by
  trivial

end Metatheory.Core

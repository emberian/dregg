import Dregg2.Paco.Basic
import Dregg2.Paco.GPaco
import Dregg2.Paco.Companion

/-!
# Coinduction Wrappers

Thin wrappers that hide plumbing for common coinduction patterns.
These provide ergonomic entry points for coinductive proofs.
-/

namespace Paco

variable {α : Type*}

/-!
## Basic Paco Coinduction
-/

/-- Simple coinduction: prove `paco F ⊥ x y` by providing a witness R.

This is the most common entry point for coinduction proofs.

**Usage:**
```lean
theorem my_bisim : paco F ⊥ x y := by
  apply coind (R := fun a b => ...)
  · -- prove R x y (witness membership)
  · -- prove ∀ a b, R a b → F R a b (post-fixpoint)
```
-/
theorem coind {F : MonoRel α} {x y : α}
    (R : Rel α)
    (witness : R x y)
    (step : ∀ a b, R a b → F R a b) :
    paco F ⊥ x y := by
  apply paco_coind F R ⊥ ?_ witness
  intro a b hab
  simp only [Rel.sup_bot]
  exact step a b hab

/-- Coinduction with accumulator.

Prove `paco F r x y` where `r` contains already-known facts.
The step function can use both the witness R and the accumulator r.

**Usage:**
```lean
theorem my_bisim : paco F r x y := by
  apply coind_acc (R := fun a b => ...)
  · -- prove R x y
  · -- prove ∀ a b, R a b → F (R ⊔ r) a b
```
-/
theorem coind_acc {F : MonoRel α} {r : Rel α} {x y : α}
    (R : Rel α)
    (witness : R x y)
    (step : ∀ a b, R a b → F (R ⊔ r) a b) :
    paco F r x y :=
  paco_coind F R r step witness

/-!
## GPaco Coinduction
-/

/-- GPaco coinduction with both base and recursive cases.

The step function can return either:
- `Or.inl h` for F-progress (recursive case using gupaco)
- `Or.inr h` for base case (in r, immediate termination)

**Usage:**
```lean
theorem my_bisim : gpaco F r g x y := by
  apply gcoind (R := fun a b => ...)
  · -- prove R x y
  · intro a b hab
    -- prove F (R ⊔ gupaco F r g) a b ∨ r a b
```
-/
theorem gcoind {F : MonoRel α} {r g : Rel α} {x y : α}
    (R : Rel α)
    (witness : R x y)
    (step : ∀ a b, R a b → F (R ⊔ gupaco F r g) a b ∨ r a b) :
    gpaco F r g x y :=
  gpaco_coind F R r g step witness

/-- GPaco coinduction (relational form).

Same as `gcoind` but returns `R ≤ gpaco F r g` instead of pointwise. -/
theorem gcoind' {F : MonoRel α} {r g : Rel α}
    (R : Rel α)
    (step : ∀ a b, R a b → F (R ⊔ gupaco F r g) a b ∨ r a b) :
    R ≤ gpaco F r g :=
  fun _ _ hxy => gpaco_coind F R r g step hxy

/-!
## Up-To Coinduction (gpaco_clo)
-/

/-- Up-to coinduction with closure operator.

This is the "cofix" variant that mirrors Coq's `gpacoN_cofix`.
The step function shows that R makes F-progress under the composed
generating function.

**Usage:**
```lean
theorem my_bisim : gpaco_clo F clo r rg x y := by
  apply upto_coind (R := fun a b => ...)
  · -- prove R x y
  · -- prove R ≤ F (rclo clo (R ⊔ upaco (F ∘ rclo clo) (rg ⊔ r))) ⊔ r
```
-/
theorem upto_coind {F : MonoRel α} {clo : Rel α → Rel α} {r rg : Rel α} {x y : α}
    (R : Rel α)
    (witness : R x y)
    (step : R ≤ F (rclo clo (R ⊔ upaco (composeRclo F clo) (rg ⊔ r))) ⊔ r) :
    gpaco_clo F clo r rg x y :=
  gpaco_clo_cofix F clo r rg R step witness

/-- Up-to coinduction with companion (canonical choice).

Uses the companion as the closure operator, which is the greatest
compatible monotone closure and works with any monotone F.

**Usage:**
```lean
theorem my_bisim : gpaco_clo F (companion F) r rg x y := by
  apply companion_coind (R := fun a b => ...)
  · -- prove R x y
  · -- prove R ≤ F (rclo (companion F) (R ⊔ upaco ... (rg ⊔ r))) ⊔ r
```
-/
theorem companion_coind {F : MonoRel α} {r rg : Rel α} {x y : α}
    (R : Rel α)
    (witness : R x y)
    (step : R ≤ F (rclo (companion F) (R ⊔ upaco (composeRclo F (companion F)) (rg ⊔ r))) ⊔ r) :
    gpaco_clo F (companion F) r rg x y :=
  upto_coind R witness step

/-!
## Convenience: Simple Up-To Coinduction

When the accumulator and guard are both ⊥.
-/

/-- Up-to coinduction for `gupaco_clo F clo ⊥`.

Simplified interface when no accumulator or guard is needed. -/
theorem upto_coind_bot {F : MonoRel α} {clo : Rel α → Rel α} {x y : α}
    (R : Rel α)
    (witness : R x y)
    (step : R ≤ F (rclo clo (R ⊔ upaco (composeRclo F clo) ⊥))) :
    gupaco_clo F clo ⊥ x y := by
  apply upto_coind R witness
  intro a b hab
  left
  have h := step a b hab
  simp only [Rel.sup_bot] at h ⊢
  exact h

/-- Companion coinduction with ⊥ accumulator/guard. -/
theorem companion_coind_bot {F : MonoRel α} {x y : α}
    (R : Rel α)
    (witness : R x y)
    (step : R ≤ F (rclo (companion F) (R ⊔ upaco (composeRclo F (companion F)) ⊥))) :
    gupaco_clo F (companion F) ⊥ x y :=
  upto_coind_bot R witness step

end Paco

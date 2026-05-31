import Dregg2.Paco.Basic
import Dregg2.Paco.GPaco

/-!
# Paco Simp Lemmas

Additional simp lemmas for common simplifications in paco proofs.
These supplement the core lemmas in Basic.lean and GPaco.lean.
-/

namespace Paco

variable {α : Type*}

/-!
## Simplification of upaco at ⊥
-/

-- upaco_bot is already @[simp] in Basic.lean

/-!
## One-step lemmas for specific F patterns

These provide iff versions useful for simp rewrites.
-/

/-- When goal is `paco F r x y`, unfold to witness form -/
@[simp] theorem paco_unfold_simp (F : MonoRel α) (r : Rel α) (x y : α) :
    paco F r x y ↔ ∃ R, (∀ a b, R a b → F (R ⊔ r) a b) ∧ R x y := Iff.rfl

/-- Specialized: paco F ⊥ as gfp -/
theorem paco_bot_eq_gfp (F : MonoRel α) :
    paco F ⊥ = F.toOrderHom.gfp := paco_bot F

/-!
## GPaco one-step lemmas
-/

/-- gpaco step at ⊥ guard simplifies to upaco step

Note: Not marked @[simp] to avoid potential loops. -/
theorem gpaco_step_bot_g (F : MonoRel α) (r : Rel α) :
    gpaco F r ⊥ = F (upaco F r) ⊔ r := by
  -- gpaco F r ⊥ = paco F (r ⊔ ⊥) ⊔ r = paco F r ⊔ r = upaco F r
  -- We want: upaco F r = F (upaco F r) ⊔ r
  -- Since upaco F r = paco F r ⊔ r and paco F r = F (upaco F r)
  calc gpaco F r ⊥ = upaco F r := gpaco_bot_g F r
    _ = paco F r ⊔ r := rfl
    _ = F (upaco F r) ⊔ r := by rw [paco_eq]

/-- gupaco at ⊥ guard simplifies to upaco -/
theorem gupaco_bot_g (F : MonoRel α) (r : Rel α) :
    gupaco F r ⊥ = upaco F r := by
  simp only [gupaco, gpaco_bot_g, Rel.sup_bot]

/-- gupaco at ⊥ available parameter -/
theorem gupaco_bot_r (F : MonoRel α) (g : Rel α) :
    gupaco F ⊥ g = upaco F g := by
  simp only [gupaco_eq_upaco, Rel.bot_sup]

/-!
## Relation simplifications
-/

/-- Simplify double sup with same relation -/
theorem sup_sup_self (R S : Rel α) : (R ⊔ S) ⊔ S = R ⊔ S := by
  ext x y; simp only [Rel.union_apply]; tauto

/-- Simplify self sup double -/
theorem self_sup_sup (R S : Rel α) : R ⊔ (R ⊔ S) = R ⊔ S := by
  ext x y; simp only [Rel.union_apply]; tauto

/-!
## Membership simplifications
-/

/-- Simplify membership in upaco -/
@[simp] theorem upaco_apply (F : MonoRel α) (r : Rel α) (x y : α) :
    upaco F r x y ↔ paco F r x y ∨ r x y := by
  simp only [upaco, Rel.union_apply]

/-- Simplify membership in gpaco -/
@[simp] theorem gpaco_apply (F : MonoRel α) (r g : Rel α) (x y : α) :
    gpaco F r g x y ↔ paco F (r ⊔ g) x y ∨ r x y := by
  simp only [gpaco, Rel.union_apply]

/-- Simplify membership in gupaco -/
@[simp] theorem gupaco_apply (F : MonoRel α) (r g : Rel α) (x y : α) :
    gupaco F r g x y ↔ paco F (r ⊔ g) x y ∨ r x y ∨ g x y := by
  simp only [gupaco, gpaco, Rel.union_apply]
  tauto

end Paco

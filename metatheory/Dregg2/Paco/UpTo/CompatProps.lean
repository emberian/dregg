import Dregg2.Paco.UpTo.Closures

/-!
# Compatibility Properties

Lightweight typeclasses that capture sufficient conditions for compatibility
results used across the up-to framework.
-/

namespace Paco

variable {α : Type*}

/-- F preserves transitive closure. -/
class PreserveTransClosure (F : MonoRel α) : Prop where
  (h : ∀ R, transClosure (F R) ≤ F (transClosure R))

/-- F is compatible with relational composition (transitive closure). -/
class CompCompatible (F : MonoRel α) : Prop where
  (comp : Compatible F (transClosure (α := α)))

/-- Preserving transitive closure implies composition compatibility. -/
instance compCompatible_of_preserve (F : MonoRel α) [PreserveTransClosure F] :
    CompCompatible F :=
  ⟨transClosure_compatible_of_preserve F (PreserveTransClosure.h (F := F))⟩

end Paco

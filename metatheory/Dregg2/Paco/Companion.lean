import Dregg2.Paco.UpTo.WCompat
import Dregg2.Paco.UpTo.Closures
import Dregg2.Paco.UpTo.CompatProps

/-!
# Companion Interface

This module provides a small, packaged interface for the companion operator.
It reuses the `cpn` construction from the up-to framework and packages the
expected fields (monotonicity, compatibility, and extensiveness).
-/

namespace Paco

variable {α : Type*}

/-- A packaged companion for a relation transformer. -/
structure Companion (F : MonoRel α) where
  /-- The companion closure operator. -/
  C : Rel α → Rel α
  /-- Monotonicity of the closure. -/
  mono : Monotone2 C
  /-- Compatibility with the generator. -/
  compat : Compatible F C
  /-- Extensiveness: R ≤ C R. -/
  extensive : ∀ R, R ≤ C R

/-!
## Canonical companion (cpn) and convenience lemmas
-/

/-- Canonical companion closure operator. -/
def companion (F : MonoRel α) : Rel α → Rel α := cpn F

/-- The canonical companion built from `cpn`. -/
def cpnCompanion (F : MonoRel α) : Companion F where
  C := companion F
  mono := cpn.cpn_cloMono
  compat := cpn.compat
  extensive := fun R => cpn.base (F := F) (R := R)

@[simp]
theorem cpnCompanion_C (F : MonoRel α) : (cpnCompanion F).C = companion F := rfl

@[simp]
theorem companion_def (F : MonoRel α) : companion F = cpn F := rfl

theorem companion_mono (F : MonoRel α) : Monotone2 (companion F) :=
  cpn.cpn_cloMono

theorem companion_extensive (F : MonoRel α) (R : Rel α) : R ≤ companion F R :=
  cpn.base (F := F) (R := R)

theorem companion_compat (F : MonoRel α) : Compatible F (companion F) :=
  cpn.compat

theorem companion_idem (F : MonoRel α) (R : Rel α) :
    companion F (companion F R) ≤ companion F R :=
  cpn.cpn_cpn (F := F) (R := R)

theorem companion_greatest (F : MonoRel α) {clo : Rel α → Rel α} {R : Rel α}
    (h_mono : CloMono clo) (h_compat : Compatible F clo) :
    clo R ≤ companion F R :=
  cpn.greatest (F := F) (R := R) h_mono h_compat

theorem companion_gupaco (F : MonoRel α) (R : Rel α) :
    gupaco_clo F (companion F) R ≤ companion F R := by
  simpa [companion] using cpn.gupaco (F := F) (R := R)

theorem companion_gupaco_eq (F : MonoRel α) (R : Rel α) :
    gupaco_clo F (companion F) R = companion F R := by
  simpa [companion] using cpn.gupaco_eq (F := F) (R := R)


/-- The companion is closed under F application: F (companion F R) ≤ companion F R.

This is a key property (cpn_step in Coq) that enables coinductive reasoning
about the companion. -/
theorem companion_step (F : MonoRel α) (R : Rel α) :
    F (companion F R) ≤ companion F R :=
  cpn.step

/-- Companion composition via transitive closure.

Assumes `transClosure` is compatible with `F`, so the companion absorbs the
transitive closure of itself and is therefore closed under composition. -/
theorem companion_compose (F : MonoRel α) (R : Rel α) [CompCompatible F] :
    ∀ a b c, companion F R a b → companion F R b c → companion F R a c := by
  intro a b c hab hbc
  have h_trans : transClosure (companion F R) a c :=
    transClosure.trans (transClosure.base hab) (transClosure.base hbc)
  have h_le : transClosure (companion F R) ≤ companion F R := by
    have h1 : transClosure (companion F R) ≤ companion F (companion F R) :=
      companion_greatest (F := F) (R := companion F R)
        (h_mono := transClosure_mono) (h_compat := (CompCompatible.comp (F := F)))
    exact Rel.le_trans h1 (companion_idem (F := F) (R := R))
  exact h_le a c h_trans

end Paco

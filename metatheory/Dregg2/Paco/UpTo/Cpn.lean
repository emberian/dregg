import Dregg2.Paco.UpTo.Compat

/-!
# Companion (cpn)

The companion is the greatest compatible closure operator. It is defined as the
union of all compatible monotone closures:

  cpn F R x y := ∃ clo, CloMono clo ∧ Compatible F clo ∧ clo R x y

Key properties:
- `cpn_mono`: cpn F is monotone
- `cpn_greatest`: Any compatible monotone clo is ≤ cpn F
- `cpn_compat`: cpn F is itself compatible with F
- `cpn_gupaco`: gupaco F (cpn F) ≤ cpn F (absorption)

References:
- [Paco Coq: cpnN](https://github.com/snu-sf/paco)
- [GPaco paper Section 4](https://paulhe.com/assets/gpaco.pdf)
-/

namespace Paco

variable {α : Type*}

/-- The companion: greatest compatible closure operator.

`cpn F R x y` holds if there exists a compatible monotone closure `clo` such that
`clo R x y`. This is the union of all compatible closures. -/
inductive cpn (F : MonoRel α) (R : Rel α) : Rel α where
  | intro (clo : Rel α → Rel α) (h_mono : CloMono clo) (h_compat : Compatible F clo)
          (h_clo : clo R x y) : cpn F R x y

namespace cpn

variable {F : MonoRel α} {R S : Rel α}

/-- cpn is monotone: if R ≤ S then cpn F R ≤ cpn F S -/
theorem mono : R ≤ S → cpn F R ≤ cpn F S := by
  intro hRS x y ⟨clo, h_mono, h_compat, h_clo⟩
  exact ⟨clo, h_mono, h_compat, h_mono R S hRS x y h_clo⟩

/-- cpn F is a monotone closure operator -/
theorem cpn_cloMono : CloMono (cpn F) := fun _ _ h => mono h

/-- Any compatible monotone closure is contained in cpn (cpn is greatest) -/
theorem greatest {clo : Rel α → Rel α} (h_mono : CloMono clo) (h_compat : Compatible F clo) :
    clo R ≤ cpn F R := fun _ _ h => ⟨clo, h_mono, h_compat, h⟩

/-- R is contained in cpn F R (via identity closure) -/
theorem base : R ≤ cpn F R := greatest cloMono_id (compatible_id F)

/-- cpn F is compatible with F -/
theorem compat : Compatible F (cpn F) := by
  intro R x y ⟨clo, h_mono, h_compat, h_clo⟩
  have h1 : clo (F R) ≤ F (clo R) := h_compat R
  have h2 : clo R ≤ cpn F R := greatest h_mono h_compat
  have h3 : F (clo R) ≤ F (cpn F R) := F.mono' h2
  exact h3 x y (h1 x y h_clo)

/-- cpn is idempotent: cpn F (cpn F R) ≤ cpn F R -/
theorem cpn_cpn : cpn F (cpn F R) ≤ cpn F R := by
  intro x y ⟨clo, h_mono, h_compat, h_clo⟩
  have h_comp_mono : CloMono (clo ∘ cpn F) := fun R S hRS =>
    h_mono (cpn F R) (cpn F S) (cpn_cloMono R S hRS)
  have h_comp_compat : Compatible F (clo ∘ cpn F) :=
    compatible_comp F h_mono h_compat compat
  have h_le : (clo ∘ cpn F) R ≤ cpn F R := greatest h_comp_mono h_comp_compat
  exact h_le x y h_clo

/-- rclo clo ≤ cpn F when clo is compatible and monotone -/
theorem rclo_le {clo : Rel α → Rel α} (h_mono : CloMono clo) (h_compat : Compatible F clo) :
    rclo clo R ≤ cpn F R := by
  intro x y h
  induction h with
  | base hr => exact base _ _ hr
  | clo R' _ hcloR' ih =>
    have h1 : clo R' ≤ cpn F R' := greatest h_mono h_compat
    have h2 : cpn F R' ≤ cpn F (cpn F R) := mono ih
    have h3 : cpn F (cpn F R) ≤ cpn F R := cpn_cpn
    exact h3 _ _ (h2 _ _ (h1 _ _ hcloR'))

/-- cpn is closed under F application: F (cpn F R) ≤ cpn F R.

This is a key lemma (cpn_step in Coq). The proof shows that F ∘ cpn F is a
compatible monotone closure, so by cpn.greatest, (F ∘ cpn F) R ≤ cpn F R. -/
theorem step : F (cpn F R) ≤ cpn F R := by
  -- Define clo = F ∘ cpn F
  let clo : Rel α → Rel α := fun X => F (cpn F X)
  -- Show clo is monotone
  have h_mono : CloMono clo := fun R S hRS => F.mono' (cpn_cloMono R S hRS)
  -- Show clo is compatible: clo (F R) ≤ F (clo R)
  -- clo (F R) = F (cpn F (F R)) ≤ F (F (cpn F R)) = F (clo R)
  -- This uses cpn.compat: cpn F (F R) ≤ F (cpn F R)
  have h_compat : Compatible F clo := by
    intro R' x y hclo
    -- hclo : clo (F R') x y = F (cpn F (F R')) x y
    -- Goal: F (clo R') x y = F (F (cpn F R')) x y
    -- By cpn.compat: cpn F (F R') ≤ F (cpn F R')
    -- By F.mono': F (cpn F (F R')) ≤ F (F (cpn F R'))
    have h_cpn_compat : cpn F (F R') ≤ F (cpn F R') := compat R'
    exact F.mono' h_cpn_compat x y hclo
  -- By cpn.greatest: clo R ≤ cpn F R
  exact greatest h_mono h_compat

end cpn

end Paco

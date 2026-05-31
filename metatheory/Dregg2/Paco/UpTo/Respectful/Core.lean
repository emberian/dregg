import Dregg2.Paco.UpTo.Cpn
import Dregg2.Paco.UpTo.GPacoClo
import Dregg2.Paco.UpTo.Compose
import Dregg2.Paco.Companion

/-!
# Respectfulness

Respectfulness provides weaker conditions than compatibility that are often easier to prove.
The Coq paco library has three forms: wrespectful, prespectful, and grespectful.

## Overview

- `Compatible' F clo`: Compatibility with extended generator (id ⊔ F)
- `WRespectful F clo`: Weak respectfulness - clo l ≤ F (rclo clo r) when l ≤ r and l ≤ F r
- `PRespectful F clo`: Paco respectfulness - clo l ≤ paco F (r ⊔ clo r) when l ≤ r and l ≤ F r
- `GRespectful F clo`: Generalized respectfulness - most general form

All forms should imply that the closure is contained in the companion.

## Key Definitions

- `extendedGen F`: The extended generator, `extendedGen F R = R ⊔ F R`
- `Compatible' F clo`: Equivalent to `Compatible (extendedGen F) clo`
- `prespectClosure F clo`: Closure operator `R ↦ upaco F (R ⊔ clo R)` used for PRespectful

## Proof Structure

The main theorem chain is:
1. `compatible'_iff_compat_extended`: Compatible' F clo ↔ Compatible (extendedGen F) clo
2. `cpn_extendedGen_compat`: cpn F is (extendedGen F)-compatible (PROVEN)
3. `cpn_le_cpn_extendedGen`: cpn F ≤ cpn (extendedGen F) (PROVEN)
4. `cpn_extendedGen_le_cpn`: cpn (extendedGen F) ≤ cpn F (requires ExtCompatImpliesCompat)
5. `cpn_eq_cpn_extendedGen`: cpn F = cpn (extendedGen F) (requires ExtCompatImpliesCompat)
6. `cpn_extendedGen_F_compat`: cpn (extendedGen F) is F-compatible (via equality + assumption)
7. `compatible'_le_companion`: Compatible' closures ≤ companion (requires ExtCompatImpliesCompat)

## Proof Status

**Fully proven:**
- `cpn_compat'`: cpn F is Compatible' (ext-compatible via specific cpn structure)
- `cpn_extendedGen_compat`: cpn F is (extendedGen F)-compatible
- `cpn_le_cpn_extendedGen`: cpn F ≤ cpn (extendedGen F)
- `cpn_extendedGen_fixed`: cpn F R is a fixed point of extendedGen F
- `compatible'_le_companion`: Compatible' closures ≤ companion (requires ExtCompatImpliesCompat)
- `compat_wrespect`: Compatibility implies weak respectfulness
- `cloMono_wrespectfulExt`: Compatible' + monotone closure implies WRespectfulExt
- `wrespect_to_ext`: WRespectful + Compatible' implies WRespectfulExt
- `wrespect_compatible'`: WRespectfulExt implies Compatible' for rclo clo
- `wrespect_companion`: WRespectfulExt implies clo ≤ companion
- `prespect_companion`, `grespect_companion`: via Compatible' + ExtCompatImpliesCompat
- `wrespect_uclo`, `prespect_uclo`, `grespect_uclo`: UClo lemmas (prespect/grespect require Compatible')
- `prespectClosure_mono`, `clo_le_prespectClosure`: Helper lemmas for PRespectful

**Open (blocked by proof-relevant tracking):**
- `prespect_compatible'` (needed for direct PRespectful → companion)
- `grespect_compatible'` (needed for direct GRespectful → companion)
**Requires assumption:**
- `cpn_extendedGen_le_cpn` (line ~205): cpn (extendedGen F) ≤ cpn F
  - Requires `ExtCompatImpliesCompat F` (see Compat.lean)

## Technical Challenge

The fundamental issue across all remaining proofs is tracking "F-guardedness" through
closure operations:

1. **Coq's constructive proofs** use proof term structure to track which branch of
   `A ⊔ B` an element came from. When proving `clo l ≤ F (...)`, the proof term
   shows the element is constructively in the F-guarded branch.

2. **Lean's classical setting** uses case analysis `cases h with | inl => ... | inr => ...`
   which loses the tracking information. After the split, we can't determine which
   branch the original element came from.

3. **The WRespectful condition** requires BOTH `l ≤ r` AND `l ≤ F r`, but induction
   hypotheses give `l ≤ r ⊔ F r` (a disjunction), not the conjunction.

## Workarounds for Users

1. **Use standard compatibility**: If your closure is Compatible F clo (the stronger
   condition), use `cpn.greatest` directly - no respectfulness needed.

2. **Use `compat_wrespect`**: Convert compatibility to weak respectfulness; use
   WRespectfulExt when the extended-generator form is available.

3. **For Compatible' closures**: Use `compatible'_le_companion` after proving
   `Compatible (extendedGen F) clo`.

4. **Direct companion construction**: Show `clo R ≤ cpn F R` by finding a compatible
   monotone closure that dominates your closure.

## Potential Solutions for Completing Proofs

1. **Proof-relevant types**: Define a refined inductive that tracks guardedness
2. **Well-founded induction**: On the depth of rclo/cpn derivations with guardedness
3. **Choice axioms**: Use choice to extract witnesses for the F-guarded case
4. **Different proof strategies**: Prove equivalent statements that avoid case analysis

## References

- [Coq paco: gpaco.v](https://github.com/snu-sf/paco) - Respectfulness definitions
- [Coq paco: cpnN_gf](https://github.com/snu-sf/paco) - Proof that cpn F = cpn (id ⊔ F)
- [GPaco paper (CPP 2020)](https://paulhe.com/assets/gpaco.pdf) - Theoretical foundations
-/

namespace Paco

variable {α : Type*}

/-!
## Compatible' (Compatibility with id ⊔ F)

This auxiliary notion is used in the Coq paco library to bridge wrespectful to companion.
Compatible' F clo means: clo (R ⊔ F R) ≤ clo R ⊔ F (clo R)

This is equivalent to compatibility with gf' = id ⊔ gf, i.e., the extended generator
that allows staying in place (id) or making F-progress.
-/

-- Note: Compatible', extendedGen, and extendedGen_def are now defined in Paco.UpTo.Compat

/-- cpn F is compatible with extendedGen F, specialized proof using cpn structure.

This is the key lemma showing cpn F satisfies the Compatible' property.
The proof uses cpn.step to absorb F (cpn F R) ≤ cpn F R. -/
theorem cpn_compat' (F : MonoRel α) : Compatible' F (cpn F) := by
  intro R
  -- Goal: cpn F (R ⊔ F R) ≤ cpn F R ⊔ F (cpn F R)
  have h_RFR_le : R ⊔ F R ≤ cpn F R := by
    apply sup_le cpn.base
    exact Rel.le_trans (F.mono' cpn.base) cpn.step
  calc cpn F (R ⊔ F R)
      ≤ cpn F (cpn F R) := cpn.mono h_RFR_le
    _ ≤ cpn F R := cpn.cpn_cpn
    _ ≤ cpn F R ⊔ F (cpn F R) := le_sup_left

/-- cpn F R is a fixed point of extendedGen F: (extendedGen F) (cpn F R) = cpn F R.

This follows from cpn.step: F (cpn F R) ≤ cpn F R, which means the F-part of
the union is absorbed. -/
theorem cpn_extendedGen_fixed (F : MonoRel α) (R : Rel α) :
    extendedGen F (cpn F R) ≤ cpn F R := by
  -- (extendedGen F) (cpn F R) = cpn F R ⊔ F (cpn F R)
  -- By cpn.step: F (cpn F R) ≤ cpn F R
  -- So the union equals cpn F R
  simp only [extendedGen_def]
  apply sup_le (Rel.le_refl _) cpn.step

/-- cpn F is (extendedGen F)-compatible.

This is the key lemma for showing cpn F = cpn (extendedGen F). The proof uses:
1. R ⊔ F R ≤ cpn F R (from cpn.base and cpn.step)
2. cpn F (R ⊔ F R) ≤ cpn F (cpn F R) by monotonicity
3. cpn F (cpn F R) ≤ cpn F R by cpn.cpn_cpn -/
theorem cpn_extendedGen_compat (F : MonoRel α) : Compatible (extendedGen F) (cpn F) := by
  intro R
  -- Goal: cpn F ((extendedGen F) R) ≤ (extendedGen F) (cpn F R)
  -- i.e., cpn F (R ⊔ F R) ≤ cpn F R ⊔ F (cpn F R)
  -- Since F (cpn F R) ≤ cpn F R (by cpn.step), the RHS equals cpn F R.
  -- So we need: cpn F (R ⊔ F R) ≤ cpn F R.
  have h_RFR_le : R ⊔ F R ≤ cpn F R := by
    apply sup_le
    · exact cpn.base  -- R ≤ cpn F R
    · -- F R ≤ F (cpn F R) ≤ cpn F R
      exact Rel.le_trans (F.mono' cpn.base) cpn.step
  calc cpn F (extendedGen F R)
      = cpn F (R ⊔ F R) := rfl
    _ ≤ cpn F (cpn F R) := cpn.mono h_RFR_le
    _ ≤ cpn F R := cpn.cpn_cpn
    _ ≤ cpn F R ⊔ F (cpn F R) := le_sup_left
    _ = extendedGen F (cpn F R) := rfl

/-- cpn F ≤ cpn (extendedGen F), since cpn F is (extendedGen F)-compatible. -/
theorem cpn_le_cpn_extendedGen (F : MonoRel α) (R : Rel α) :
    cpn F R ≤ cpn (extendedGen F) R :=
  cpn.greatest cpn.cpn_cloMono (cpn_extendedGen_compat F)

/-- F R ≤ cpn F R via base and step.

This helper shows that F R is contained in cpn F R, which is key for
showing cpn (extendedGen F) is F-compatible. -/
theorem F_le_cpn (F : MonoRel α) (R : Rel α) : F R ≤ cpn F R := by
  -- F R ≤ F (cpn F R) by F.mono (since R ≤ cpn F R by cpn.base)
  -- F (cpn F R) ≤ cpn F R by cpn.step
  exact Rel.le_trans (F.mono' cpn.base) cpn.step

/-- extendedGen F (cpn F R) = cpn F R (cpn F R is a fixed point of extendedGen F).

Since F (cpn F R) ≤ cpn F R by cpn.step, we have:
extendedGen F (cpn F R) = cpn F R ⊔ F (cpn F R) = cpn F R -/
theorem cpn_extendedGen_fixedpoint (F : MonoRel α) (R : Rel α) :
    extendedGen F (cpn F R) = cpn F R := by
  apply Rel.le_antisymm
  · -- extendedGen F (cpn F R) ≤ cpn F R
    exact cpn_extendedGen_fixed F R
  · -- cpn F R ≤ extendedGen F (cpn F R) = cpn F R ⊔ F (cpn F R)
    exact le_sup_left

/-- If extendedGen-compatible closures are already F-compatible, then
    the extended-generator companion is bounded by the original companion. -/
theorem cpn_extendedGen_le_cpn (F : MonoRel α) (R : Rel α)
    [h_ext : ExtCompatImpliesCompat F] :
    cpn (extendedGen F) R ≤ cpn F R := by
  intro x y hcpn
  obtain ⟨clo, h_mono, h_compat_ext, h_clo⟩ := hcpn
  have h_compat : Compatible F clo := h_ext.h clo h_mono h_compat_ext
  exact cpn.greatest h_mono h_compat x y h_clo

/-- cpn F = cpn (extendedGen F).

The companions for F and (extendedGen F) = (id ⊔ F) are equal. This is because:
- cpn F is (extendedGen F)-compatible (cpn_extendedGen_compat)
- Any (extendedGen F)-compatible closure stays within cpn F R -/
theorem cpn_eq_cpn_extendedGen (F : MonoRel α) (R : Rel α)
    [ExtCompatImpliesCompat F] :
    cpn F R = cpn (extendedGen F) R :=
  Rel.le_antisymm (cpn_le_cpn_extendedGen F R) (cpn_extendedGen_le_cpn F R)

/-- cpn (extendedGen F) is F-compatible, by equality with cpn F. -/
theorem cpn_extendedGen_F_compat (F : MonoRel α) [ExtCompatImpliesCompat F] :
    Compatible F (cpn (extendedGen F)) := by
  intro R
  -- Rewrite both occurrences of cpn F using the cpn equality at R and F R.
  simpa [cpn_eq_cpn_extendedGen (F := F) (R := R),
         cpn_eq_cpn_extendedGen (F := F) (R := F R)] using
    (cpn.compat (F := F) (R := R))

-- Note: compatible'_iff_compat_extended is now compatible'_iff_compat_extendedGen in Compat.lean

/-- Compatible' closures are contained in the companion.

Following Coq's approach (cpnN_from_compatible'):
1. Compatible' F clo = Compatible (extendedGen F) clo
2. By cpn.greatest for extendedGen: clo ≤ cpn (extendedGen F)
3. By cpn_eq_cpn_extendedGen (with ExtCompatImpliesCompat): cpn (extendedGen F) = cpn F

This avoids the circular dependency by working with the extended generator
and using the key equality cpn F = cpn (extendedGen F). -/
theorem compatible'_le_companion (F : MonoRel α) {clo : Rel α → Rel α}
    (h_mono : CloMono clo) (h_compat' : Compatible' F clo)
    [ExtCompatImpliesCompat F] :
    ∀ R, clo R ≤ companion F R := by
  intro R
  -- Step 1: clo is compatible with extendedGen F (by hypothesis)
  have h_compat_ext : Compatible (extendedGen F) clo :=
    (compatible'_iff_compat_extendedGen F clo).mp h_compat'
  -- Step 2: By cpn.greatest, clo ≤ cpn (extendedGen F)
  have h_clo_le_cpn_ext : clo R ≤ cpn (extendedGen F) R :=
    cpn.greatest h_mono h_compat_ext
  -- Step 3: cpn (extendedGen F) = cpn F
  have h_cpn_eq : cpn (extendedGen F) R = cpn F R := (cpn_eq_cpn_extendedGen F R).symm
  -- Combine: clo R ≤ cpn (extendedGen F) R = cpn F R = companion F R
  rw [h_cpn_eq] at h_clo_le_cpn_ext
  exact h_clo_le_cpn_ext

end Paco

import Dregg2.Paco.Basic
import Dregg2.Paco.UpTo.GPacoClo

/-!
# Coq Paco Naming Compatibility

This module provides naming aliases for users familiar with the Coq paco library.
The aliases map Coq names to their Lean equivalents.

## Naming Conventions

| Coq Name           | Lean Name          | Description                     |
|--------------------|--------------------|---------------------------------|
| `paco_mult`        | `paco_acc`         | `paco F (paco F r) ≤ paco F r`  |
| `paco_mult_strong` | `paco_acc_upaco`   | `paco F (upaco F r) ≤ paco F r` |
| `gpaco_mult`       | `gpaco_clo_gupaco` | Gupaco absorption               |

## References

- [Coq paco library](https://github.com/snu-sf/paco)
-/

namespace Paco

variable {α : Type*}

/-!
## Mult Lemmas (Accumulation)

In Coq paco, "mult" refers to the property that paco can absorb itself,
analogous to idempotence. In Lean paco, this is called "accumulation" (acc).
-/

/-- Alias for `paco_acc` (Coq: `paco_mult`).

`paco F (paco F r) ≤ paco F r` - paco can absorb itself in the parameter. -/
theorem paco_mult (F : MonoRel α) (r : Rel α) :
    paco F (paco F r) ≤ paco F r :=
  paco_acc F r

/-- Alias for `paco_acc_upaco` (Coq: `paco_mult_strong`).

`paco F (upaco F r) ≤ paco F r` - the stronger version absorbs upaco. -/
theorem paco_mult_strong (F : MonoRel α) (r : Rel α) :
    paco F (upaco F r) ≤ paco F r :=
  paco_acc_upaco F r

/-!
## GPaco Mult Lemmas
-/

/-- Alias for `gpaco_clo_gupaco` (Coq: `gpaco_gupaco`).

Absorbs gupaco_clo in the first parameter of gpaco_clo. -/
theorem gpaco_clo_mult (F : MonoRel α) (clo : Rel α → Rel α)
    (h_mono : CloMono clo) (h_compat : Compatible F clo)
    (r rg : Rel α) :
    gupaco_clo F clo (gpaco_clo F clo r rg) ≤ gpaco_clo F clo r rg :=
  gpaco_clo_gupaco F clo h_mono h_compat r rg

/-!
## Unfold/Fold Aliases

The Coq library uses `paco_unfold` and `paco_fold` which match our naming.
-/

/-- Alias confirming `paco_unfold` matches Coq naming. -/
theorem paco_destruct (F : MonoRel α) (r : Rel α) :
    paco F r ≤ F (upaco F r) :=
  paco_unfold F r

/-- Alias confirming `paco_fold` matches Coq naming. -/
theorem paco_construct (F : MonoRel α) (r : Rel α) :
    F (upaco F r) ≤ paco F r :=
  paco_fold F r

/-!
## Monotonicity Aliases
-/

/-- Alias for `paco_mon` (Coq: `paco_mon_gen` or similar).

Paco is monotone in its parameter. -/
theorem paco_monotone (F : MonoRel α) {r s : Rel α} (h : r ≤ s) :
    paco F r ≤ paco F s :=
  paco_mon F h

/-- Alias for `upaco_mon`.

Upaco is monotone in its parameter. -/
theorem upaco_monotone (F : MonoRel α) {r s : Rel α} (h : r ≤ s) :
    upaco F r ≤ upaco F s :=
  upaco_mon F h

end Paco

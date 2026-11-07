/-
# Market.SddPsd — exact symmetric diagonal-dominance admission implies PSD.

fhIR admits the canonical `10^-9` fixed-point covariance only after checking
exact symmetry, a nonnegative diagonal, and row-wise diagonal dominance.  This
file proves the mathematical gate for exact integer matrices.  It does not
claim that Rust's f64 canonicalization, rounding, bounds checks, or row-major
parser refine this checker; that remains a separate executable-denotation seam.
-/

import Market.CertQp
import Dregg2.Tactics
import Mathlib.Tactic

namespace Market.SddPsd

set_option autoImplicit false

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Exact mathematical SDD certificate over the rationals. -/
structure SymmetricDiagonallyDominant (P : Matrix ι ι ℚ) : Prop where
  symm : Matrix.IsSymm P
  diag_nonneg : ∀ i, 0 ≤ P i i
  row_dominant : ∀ i, (∑ j ∈ Finset.univ.erase i, |P i j|) ≤ P i i

/-- The two-variable square inequality used for each symmetric off-diagonal
pair. -/
theorem offdiag_pair_nonneg (a x y : ℚ) :
    0 ≤ 2 * a * x * y + |a| * x ^ 2 + |a| * y ^ 2 := by
  by_cases ha : 0 ≤ a
  · rw [abs_of_nonneg ha]
    nlinarith [mul_nonneg ha (sq_nonneg (x + y))]
  · have hna : a ≤ 0 := le_of_not_ge ha
    rw [abs_of_nonpos hna]
    nlinarith [mul_nonneg (neg_nonneg.mpr hna) (sq_nonneg (x - y))]

def rowRadius (P : Matrix ι ι ℚ) (i : ι) : ℚ :=
  ∑ j ∈ Finset.univ.erase i, |P i j|

def diagonalEnergy (P : Matrix ι ι ℚ) (x : ι → ℚ) : ℚ :=
  ∑ i, P i i * x i ^ 2

def radiusEnergy (P : Matrix ι ι ℚ) (x : ι → ℚ) : ℚ :=
  ∑ i, rowRadius P i * x i ^ 2

def offdiagEnergy (P : Matrix ι ι ℚ) (x : ι → ℚ) : ℚ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, P i j * x i * x j

theorem diagonalEnergy_ge_radiusEnergy
    {P : Matrix ι ι ℚ} (h : SymmetricDiagonallyDominant P) (x : ι → ℚ) :
    radiusEnergy P x ≤ diagonalEnergy P x := by
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_right (h.row_dominant i) (sq_nonneg (x i))

theorem swapped_radiusEnergy_eq
    {P : Matrix ι ι ℚ} (h : Matrix.IsSymm P) (x : ι → ℚ) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, |P i j| * x j ^ 2) = radiusEnergy P x := by
  have hfull :
      (∑ i, ∑ j, |P i j| * x j ^ 2) =
        ∑ i, ∑ j, |P i j| * x i ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    rw [h.apply j i]
  unfold radiusEnergy rowRadius
  simp_rw [Finset.sum_erase_eq_sub (Finset.mem_univ _), sub_mul]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp_rw [Finset.sum_mul]
  rw [hfull]

theorem offdiag_plus_radius_nonneg
    {P : Matrix ι ι ℚ} (h : Matrix.IsSymm P) (x : ι → ℚ) :
    0 ≤ offdiagEnergy P x + radiusEnergy P x := by
  have hsum : 0 ≤
      ∑ i, ∑ j ∈ Finset.univ.erase i,
        (2 * P i j * x i * x j + |P i j| * x i ^ 2 + |P i j| * x j ^ 2) := by
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    exact offdiag_pair_nonneg (P i j) (x i) (x j)
  have hcross :
      (∑ i, ∑ j ∈ Finset.univ.erase i, 2 * P i j * x i * x j) =
        2 * offdiagEnergy P x := by
    unfold offdiagEnergy
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hrow :
      (∑ i, ∑ j ∈ Finset.univ.erase i, |P i j| * x i ^ 2) =
        radiusEnergy P x := by
    unfold radiusEnergy rowRadius
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_mul]
  have hswap :
      (∑ i, ∑ j ∈ Finset.univ.erase i, |P i j| * x j ^ 2) =
        radiusEnergy P x := swapped_radiusEnergy_eq h x
  simp_rw [Finset.sum_add_distrib] at hsum
  rw [hcross, hrow, hswap] at hsum
  linarith

theorem quadForm_eq_diagonal_add_offdiag (P : Matrix ι ι ℚ) (x : ι → ℚ) :
    Market.quadForm P x = diagonalEnergy P x + offdiagEnergy P x := by
  rw [Market.quadForm]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  calc
    (∑ i, ∑ j, x i * (P i j * x j)) =
        ∑ i, (x i * (P i i * x i) +
          ∑ j ∈ Finset.univ.erase i, x i * (P i j * x j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (Finset.add_sum_erase Finset.univ
        (fun j => x i * (P i j * x j)) (Finset.mem_univ i)).symm
    _ = diagonalEnergy P x + offdiagEnergy P x := by
      simp only [Finset.sum_add_distrib, diagonalEnergy, offdiagEnergy]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi
      · ring
      · apply Finset.sum_congr rfl
        intro j hj
        ring

/-- Symmetric nonnegative-diagonal row dominance is a sufficient PSD
certificate for the exact rational matrix. -/
theorem sdd_implies_psd {P : Matrix ι ι ℚ}
    (h : SymmetricDiagonallyDominant P) : Market.PsdSymm P := by
  refine ⟨h.symm, ?_⟩
  intro x
  rw [quadForm_eq_diagonal_add_offdiag]
  have hdiag := diagonalEnergy_ge_radiusEnergy h x
  have hoff := offdiag_plus_radius_nonneg h.symm x
  linarith

/-! ## Executable exact-integer checker used as the formal admission surface. -/

def liftInt {n : Nat} (P : Matrix (Fin n) (Fin n) Int) :
    Matrix (Fin n) (Fin n) ℚ := fun i j => P i j

/-- Symmetry of an integer matrix is decidable entrywise. Stated for `Matrix` so instance search
does not have to abstract `P i j` over the (non-reducible) `Matrix` synonym. -/
instance decidableSymmEntries {n : Nat} (P : Matrix (Fin n) (Fin n) Int) :
    Decidable (∀ i j, P i j = P j i) :=
  @Fintype.decidableForallFintype (Fin n) (fun i => ∀ j, P i j = P j i)
    (fun i => @Fintype.decidableForallFintype (Fin n) (fun j => P i j = P j i)
      (fun j => Int.decEq (P i j) (P j i)) _) _

def sddCheck {n : Nat} (P : Matrix (Fin n) (Fin n) Int) : Bool :=
  decide (
    (∀ i j, P i j = P j i) ∧
    (∀ i, 0 ≤ P i i ∧ (∑ j ∈ Finset.univ.erase i, |P i j|) ≤ P i i))

theorem sddCheck_iff {n : Nat} (P : Matrix (Fin n) (Fin n) Int) :
    sddCheck P = true ↔
      (∀ i j, P i j = P j i) ∧
      (∀ i, 0 ≤ P i i ∧ (∑ j ∈ Finset.univ.erase i, |P i j|) ≤ P i i) := by
  simp [sddCheck]

theorem sddCheck_implies_psd {n : Nat} {P : Matrix (Fin n) (Fin n) Int}
    (hcheck : sddCheck P = true) : Market.PsdSymm (liftInt P) := by
  apply sdd_implies_psd
  have h := (sddCheck_iff P).mp hcheck
  refine ⟨?_, ?_, ?_⟩
  · apply Matrix.IsSymm.ext_iff.mpr
    intro i j
    simp only [liftInt]
    exact_mod_cast h.1 j i
  · intro i
    simp only [liftInt]
    exact_mod_cast (h.2 i).1
  · intro i
    simp only [liftInt]
    exact_mod_cast (h.2 i).2

def accepted2 : Matrix (Fin 2) (Fin 2) Int := !![4, -1; -1, 2]
def asymmetric2 : Matrix (Fin 2) (Fin 2) Int := !![4, -1; 0, 2]
def indefinite2 : Matrix (Fin 2) (Fin 2) Int := !![1, 2; 2, 1]
def negativeDiag2 : Matrix (Fin 2) (Fin 2) Int := !![-1, 0; 0, 1]
/-- PSD but deliberately outside the supported SDD admission family. -/
def psdOutsideSdd2 : Matrix (Fin 2) (Fin 2) Int := !![1, 2; 2, 4]

#guard sddCheck accepted2
#guard !sddCheck asymmetric2
#guard !sddCheck indefinite2
#guard !sddCheck negativeDiag2
#guard !sddCheck psdOutsideSdd2

theorem accepted2_psd : Market.PsdSymm (liftInt accepted2) :=
  sddCheck_implies_psd rfl

theorem asymmetric2_refused : sddCheck asymmetric2 = false := rfl
theorem indefinite2_refused : sddCheck indefinite2 = false := rfl
theorem negativeDiag2_refused : sddCheck negativeDiag2 = false := rfl
theorem psdOutsideSdd2_refused : sddCheck psdOutsideSdd2 = false := rfl

/-- The gate is sufficient, not complete: this rank-one PSD matrix is refused
because its first row is not diagonally dominant. -/
theorem psdOutsideSdd2_is_psd : Market.PsdSymm (liftInt psdOutsideSdd2) := by
  refine ⟨?_, ?_⟩
  · apply Matrix.IsSymm.ext_iff.mpr
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [liftInt, psdOutsideSdd2]
  · intro z
    simp [Market.quadForm, liftInt, psdOutsideSdd2, dotProduct, Matrix.mulVec]
    nlinarith [sq_nonneg (z 0 + 2 * z 1)]

#assert_axioms offdiag_pair_nonneg
#assert_axioms swapped_radiusEnergy_eq
#assert_axioms offdiag_plus_radius_nonneg
#assert_axioms quadForm_eq_diagonal_add_offdiag
#assert_axioms sdd_implies_psd
#assert_axioms sddCheck_iff
#assert_axioms sddCheck_implies_psd
#assert_axioms accepted2_psd
#assert_axioms psdOutsideSdd2_is_psd

/- The executable admission predicate is only exact integer symmetry and row
dominance. Convex-QP soundness may consume its theorem, but cannot silently
become part of the parser/checker itself. -/
-- POSITIVE CONTROL for the rejector below: `sddCheck_implies_psd` routes through both of these in
-- its proof term and neither in its statement, so a blind walk reds here.
#assert_depends_on Market.SddPsd.sddCheck_implies_psd
  [Market.SddPsd.sdd_implies_psd, Market.SddPsd.sddCheck_iff]

#assert_not_depends_on Market.SddPsd.sddCheck [
  Market.PsdSymm,
  Market.quadForm,
  Market.qp_certifies_epsilon_optimal]

#assert_all_clean [
  Market.SddPsd.offdiag_pair_nonneg,
  Market.SddPsd.swapped_radiusEnergy_eq,
  Market.SddPsd.offdiag_plus_radius_nonneg,
  Market.SddPsd.quadForm_eq_diagonal_add_offdiag,
  Market.SddPsd.sdd_implies_psd,
  Market.SddPsd.sddCheck_iff,
  Market.SddPsd.sddCheck_implies_psd,
  Market.SddPsd.accepted2_psd,
  Market.SddPsd.asymmetric2_refused,
  Market.SddPsd.indefinite2_refused,
  Market.SddPsd.negativeDiag2_refused,
  Market.SddPsd.psdOutsideSdd2_refused,
  Market.SddPsd.psdOutsideSdd2_is_psd]

end Market.SddPsd

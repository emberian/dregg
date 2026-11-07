import Mathlib
import Dregg2.Tactics

/-!
# The Polishchuk–Spielman bivariate divisibility lemma (Cramer–Nardi-fixed form)

This file proves **BCIKS20 Lemma 4.3** (eprint 2020/654, **revision 3**, ECCC TR20-083 rev.3,
Appendix D) — the Polishchuk–Spielman lemma [PS94] in its *corrected* form. The original
[Spi95, Lemma 4.2.18] has a known subtle gap with genuine counterexamples (cf. [Bég19]);
the fix (due to Ronald Cramer, independently of Cramer–Nardi's diagnosis) adds the hypothesis
that the per-line quotients have degree bounded by the *difference* of the (formal) degree
bounds of `B` and `A`. **The fixed statement is what this file formalizes** — note that the
rev.1 statement of Lemma 4.3 (plain divisibility on lines, hypotheses
`deg_X A + deg_X B < n_X` etc.) is superseded; the correct statement carries the
quotient-degree bounds and the pure budget `b_X/n_X + b_Z/n_Z < 1`.

## Representation

A bivariate polynomial is `F[X][Y]` (`Polynomial (Polynomial F)`, Mathlib's
`Polynomial.Bivariate` scope): the *inner* variable is `X` ("X" of BCIKS), the *outer*
variable is `Y` ("Z" of BCIKS).

* outer degree (`deg_Z`) = `Polynomial.natDegree`
* inner degree (`deg_X`) = `sdeg p := (Polynomial.Bivariate.swap p).natDegree`
* vertical line at `x` (`A(x, Z)`) = `p.map (evalRingHom x) : Polynomial F`
* horizontal line at `z` (`A(X, z)`) = `p.eval (C z) : Polynomial F`

## The proof

After splitting off `G := gcd A B` (the reduction shrinks each line count by at most the
corresponding degree of `G` and the budget survives, `budget_shrink`), the coprime pair
`(A₁, B₁)` is shown to have `A₁` *constant* by a resultant count (`coprime_core`):

* `R₀ := Res_X(A₁, B₁)`, the Sylvester resultant with formal `X`-degrees
  `(deg_X A₁, b_X)`, is a polynomial in `Z` of degree `≤ deg_X A₁ · b_Z + b_X · deg_Z A₁`
  (`natDegree_resultant_le`, a permutation-expansion bound on the Sylvester determinant);
* `R₀ ≠ 0` because the pair stays coprime over `F(Z)` (Gauss's lemma,
  `isCoprime_map_of_isRelPrime`) and the formal-degree slack on the `B`-side only
  contributes leading-coefficient factors (`Polynomial.resultant_add_right_deg`);
* — the crux — `(Z − z)^{deg_X A₁} ∣ R₀` at every good horizontal line `z`
  (`pow_X_sub_C_dvd_resultant`): the bounded-degree quotient `q` lifts to `F[X][Z]` and the
  row operation `B ↦ B − A·q̃` (legal inside the Sylvester matrix *precisely because* of the
  Cramer quotient-degree bound — the exact point where Spielman's original proof was wrong;
  in Mathlib's API this is `Polynomial.resultant_add_mul_right`) makes every entry of the
  `B`-block divisible by `Z − z`, so multilinearity (`Polynomial.resultant_C_mul_right`)
  extracts `(Z − z)^{deg_X A₁}`.

Counting the two directions against the budget (`budget_aux`) forces `A₁` constant, and the
quotient degree bounds in the conclusion come from one good line each (`sdeg_quotient_le`).

Main results:

* `Dregg2.PS.polishchuk_spielman` — **L3.2**, the fixed BCIKS20 Lemma 4.3, with the
  quotient degree bounds in the conclusion.
* `Dregg2.PS.leadingCoeff_degree_comparison` — **L3.1**, the BCIKS20 rev.1 Appendix D
  leading-coefficient degree comparison (`deg_X A ≤ deg_X B` from enough horizontal lines),
  the bridge from plain-divisibility hypotheses to the `d_X = b_X - a_X` parametrization.
* `Dregg2.PS.polishchuk_spielman_fires` — a non-vacuity instance over `ZMod 11` exercising
  every hypothesis of the main theorem on a concrete pair of bivariate polynomials.

No `sorry`, no `axiom`; `#assert_axioms` pins the keystones kernel-clean.
-/

open Polynomial
open scoped Polynomial.Bivariate

namespace Dregg2
namespace PS

variable {F : Type*} [Field F]

/-! ## Inner degree (`deg_X`) API via `Polynomial.Bivariate.swap` -/

/-- Coefficient exchange under `Polynomial.Bivariate.swap`:
`(swap p)_{i,j} = p_{j,i}` (outer index first). -/
theorem swap_coeff_coeff (p : F[X][Y]) (i j : ℕ) :
    ((Polynomial.Bivariate.swap p).coeff i).coeff j = (p.coeff j).coeff i := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a =>
    induction a using Polynomial.induction_on' with
    | add a b ha hb =>
      have hsplit : (monomial n (a + b) : F[X][Y]) = monomial n a + monomial n b :=
        map_add _ a b
      rw [hsplit, map_add]
      simp [ha, hb]
    | monomial m c =>
      rw [Polynomial.Bivariate.swap_monomial_monomial]
      by_cases hmi : m = i <;> by_cases hnj : n = j <;>
        simp [coeff_monomial, hmi, hnj]

/-- The inner (`X`-) degree of a bivariate polynomial. -/
noncomputable def sdeg (p : F[X][Y]) : ℕ := (Polynomial.Bivariate.swap p).natDegree

theorem sdeg_def (p : F[X][Y]) : sdeg p = (Polynomial.Bivariate.swap p).natDegree := rfl

@[simp] theorem sdeg_zero : sdeg (0 : F[X][Y]) = 0 := by
  simp [sdeg]

theorem swap_ne_zero {p : F[X][Y]} (hp : p ≠ 0) : Polynomial.Bivariate.swap p ≠ 0 := by
  intro h
  apply hp
  have := congrArg (Polynomial.Bivariate.swap (R := F)) h
  rwa [Polynomial.Bivariate.swap_swap_apply, map_zero] at this

@[simp] theorem sdeg_swap (p : F[X][Y]) :
    sdeg (Polynomial.Bivariate.swap p) = p.natDegree := by
  rw [sdeg_def, Polynomial.Bivariate.swap_swap_apply]

/-- Every outer coefficient of `p` has degree at most `sdeg p`. -/
theorem coeff_natDegree_le_sdeg (p : F[X][Y]) (n : ℕ) :
    (p.coeff n).natDegree ≤ sdeg p := by
  by_cases h : p.coeff n = 0
  · simp [h]
  · have hlc : (p.coeff n).coeff (p.coeff n).natDegree ≠ 0 := by
      have := Polynomial.leadingCoeff_ne_zero.mpr h
      simpa only [Polynomial.leadingCoeff] using this
    have hsw : ((Polynomial.Bivariate.swap p).coeff (p.coeff n).natDegree).coeff n ≠ 0 := by
      rw [swap_coeff_coeff]; exact hlc
    have : (Polynomial.Bivariate.swap p).coeff (p.coeff n).natDegree ≠ 0 :=
      fun h0 => hsw (by simp [h0])
    exact Polynomial.le_natDegree_of_ne_zero this

/-- Conversely, a uniform bound on the outer coefficients bounds `sdeg`. -/
theorem sdeg_le_of_coeff_natDegree_le {p : F[X][Y]} {m : ℕ}
    (h : ∀ n, (p.coeff n).natDegree ≤ m) : sdeg p ≤ m := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  ext n
  rw [swap_coeff_coeff]
  simp only [Polynomial.coeff_zero]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (h n) hk)

theorem sdeg_mul {p q : F[X][Y]} (hp : p ≠ 0) (hq : q ≠ 0) :
    sdeg (p * q) = sdeg p + sdeg q := by
  unfold sdeg
  rw [map_mul]
  exact Polynomial.natDegree_mul (swap_ne_zero hp) (swap_ne_zero hq)

/-- `swap` exchanges the two kinds of line evaluation:
mapping the coefficients of `swap p` by `eval t` is evaluating the outer variable
of `p` at `C t`. -/
theorem swap_map_evalRingHom (t : F) (p : F[X][Y]) :
    (Polynomial.Bivariate.swap p).map (evalRingHom t) = p.eval (C t) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a =>
    rw [Polynomial.Bivariate.swap_monomial, Polynomial.map_mul, eval_monomial,
      Polynomial.map_map, Polynomial.map_C]
    have hcomp : (evalRingHom t).comp (Polynomial.C (R := F)) = RingHom.id F := by
      ext x
      simp
    rw [hcomp, Polynomial.map_id]
    simp [map_pow]

/-- The vertical line of `p` is the horizontal line of `swap p`. -/
theorem map_evalRingHom_eq_eval_swap (x : F) (p : F[X][Y]) :
    p.map (evalRingHom x) = (Polynomial.Bivariate.swap p).eval (C x) := by
  have := swap_map_evalRingHom x (Polynomial.Bivariate.swap p)
  rwa [Polynomial.Bivariate.swap_swap_apply] at this

/-- The degree of a horizontal line is at most the inner degree. -/
theorem natDegree_eval_C_le (p : F[X][Y]) (z : F) :
    (p.eval (C z)).natDegree ≤ sdeg p := by
  rw [← swap_map_evalRingHom, sdeg_def]
  exact Polynomial.natDegree_map_le

/-! ## Line-vanishing counting lemmas -/

/-- A nonzero univariate polynomial has at most `natDegree` roots in any finite set. -/
theorem card_filter_eval_zero_le (T : Finset F) {c : Polynomial F} (hc : c ≠ 0)
    [DecidablePred fun z => c.eval z = 0] :
    (T.filter fun z => c.eval z = 0).card ≤ c.natDegree := by
  classical
  have hsub : (T.filter fun z => c.eval z = 0) ⊆ c.roots.toFinset := by
    intro z hz
    rw [Finset.mem_filter] at hz
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hc]
    exact hz.2
  calc (T.filter fun z => c.eval z = 0).card
      ≤ c.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card c.roots := Multiset.toFinset_card_le _
    _ ≤ c.natDegree := Polynomial.card_roots' c

/-- A nonzero bivariate polynomial vanishes identically on at most `sdeg p` vertical
lines: `#{x ∈ T : p(x, ·) = 0} ≤ sdeg p`. -/
theorem card_filter_vertical_zero_le (T : Finset F) {p : F[X][Y]} (hp : p ≠ 0)
    [DecidablePred fun x => p.map (evalRingHom x) = 0] :
    (T.filter fun x => p.map (evalRingHom x) = 0).card ≤ sdeg p := by
  classical
  set c : Polynomial F := p.coeff p.natDegree with hc
  have hc0 : c ≠ 0 := by
    have := Polynomial.leadingCoeff_ne_zero.mpr hp
    simpa only [Polynomial.leadingCoeff, hc] using this
  have hsub : (T.filter fun x => p.map (evalRingHom x) = 0) ⊆
      (T.filter fun x => c.eval x = 0) := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    refine ⟨hx.1, ?_⟩
    have hz : (p.map (evalRingHom x)).coeff p.natDegree = 0 := by rw [hx.2]; simp
    rw [Polynomial.coeff_map] at hz
    exact hz
  calc (T.filter fun x => p.map (evalRingHom x) = 0).card
      ≤ (T.filter fun x => c.eval x = 0).card := Finset.card_le_card hsub
    _ ≤ c.natDegree := card_filter_eval_zero_le T hc0
    _ ≤ sdeg p := coeff_natDegree_le_sdeg p _

/-- A nonzero bivariate polynomial vanishes identically on at most `p.natDegree` horizontal
lines: `#{z ∈ T : p(·, z) = 0} ≤ deg_Z p`. -/
theorem card_filter_horizontal_zero_le (T : Finset F) {p : F[X][Y]} (hp : p ≠ 0)
    [DecidablePred fun z => p.eval (C z) = 0] :
    (T.filter fun z => p.eval (C z) = 0).card ≤ p.natDegree := by
  classical
  have h := card_filter_vertical_zero_le T (swap_ne_zero hp)
  rw [sdeg_swap] at h
  have heq : (T.filter fun z => p.eval (C z) = 0)
      = (T.filter fun x => (Polynomial.Bivariate.swap p).map (evalRingHom x) = 0) := by
    apply Finset.filter_congr
    intro z _
    rw [swap_map_evalRingHom]
  rw [heq]
  exact h

/-! ## L3.1 — the leading-coefficient degree comparison -/

/-- **L3.1** (BCIKS20 rev.1 Appendix D): if `A(X,z) ∣ B(X,z)` on more than
`deg_Z A + deg_Z B` horizontal lines and `B ≠ 0`, then `deg_X A ≤ deg_X B`.
This is the bridge from plain-divisibility hypotheses to the `d_X = b_X - a_X`
quotient-degree parametrization of the fixed Lemma 4.3. -/
theorem leadingCoeff_degree_comparison (A B : F[X][Y]) (hB : B ≠ 0) (S : Finset F)
    (hdiv : ∀ z ∈ S, A.eval (C z) ∣ B.eval (C z))
    (hcard : A.natDegree + B.natDegree < S.card) :
    sdeg A ≤ sdeg B := by
  classical
  rcases eq_or_ne A 0 with rfl | hA
  · simp
  set c : Polynomial F := (Polynomial.Bivariate.swap A).leadingCoeff with hc
  have hc0 : c ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr (swap_ne_zero hA)
  have hcdeg : c.natDegree ≤ A.natDegree := by
    have h1 := coeff_natDegree_le_sdeg (Polynomial.Bivariate.swap A)
      (Polynomial.Bivariate.swap A).natDegree
    rw [sdeg_swap] at h1
    exact h1
  set bad1 := S.filter (fun z => c.eval z = 0) with hbad1
  set bad2 := S.filter (fun z => B.eval (C z) = 0) with hbad2
  have hb1 : bad1.card ≤ A.natDegree := le_trans (card_filter_eval_zero_le S hc0) hcdeg
  have hb2 : bad2.card ≤ B.natDegree := card_filter_horizontal_zero_le S hB
  have hex : ∃ z ∈ S, z ∉ bad1 ∪ bad2 := by
    rw [← Finset.not_subset]
    intro hsub
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le bad1 bad2
    omega
  obtain ⟨z, hzS, hzbad⟩ := hex
  rw [Finset.mem_union, not_or] at hzbad
  obtain ⟨hz1, hz2⟩ := hzbad
  have hz1' : c.eval z ≠ 0 := fun h => hz1 (Finset.mem_filter.mpr ⟨hzS, h⟩)
  have hz2' : B.eval (C z) ≠ 0 := fun h => hz2 (Finset.mem_filter.mpr ⟨hzS, h⟩)
  have hAline : (A.eval (C z)).natDegree = sdeg A := by
    rw [← swap_map_evalRingHom, sdeg_def]
    exact Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hz1'
  calc sdeg A = (A.eval (C z)).natDegree := hAline.symm
    _ ≤ (B.eval (C z)).natDegree := Polynomial.natDegree_le_of_dvd (hdiv z hzS) hz2'
    _ ≤ sdeg B := natDegree_eval_C_le B z

/-! ## The resultant machinery

We treat `p : F[X][Y]` simultaneously as an element of `R[W]` with `R := F[X]`
(coefficient ring = polynomials in the inner variable, `W` = the outer variable).
`Polynomial.resultant (swap A) (swap B) m n : F[X]` is then the Sylvester resultant
`Res_X(A,B)` eliminating the *inner* variable, a polynomial in the *outer* one. -/

/-- Degree bound for the determinant of a matrix of polynomials with per-column
degree bounds. -/
theorem natDegree_det_le {N : ℕ} (M : Matrix (Fin N) (Fin N) (Polynomial F))
    (d : Fin N → ℕ) (h : ∀ i j, (M i j).natDegree ≤ d j) :
    M.det.natDegree ≤ ∑ j, d j := by
  rw [Matrix.det_apply']
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun σ _ => ?_)
  refine le_trans Polynomial.natDegree_mul_le ?_
  rw [Polynomial.natDegree_intCast, zero_add]
  refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
  exact Finset.sum_le_sum (fun j _ => h (σ j) j)

/-- Per-entry degree bound for the Sylvester matrix: the first `m` columns carry
coefficients of `g`, the last `n` columns coefficients of `f`. -/
theorem natDegree_sylvester_entry_le (f g : F[X][Y]) (m n df dg : ℕ)
    (hf : ∀ k, (f.coeff k).natDegree ≤ df) (hg : ∀ k, (g.coeff k).natDegree ≤ dg)
    (i j : Fin (m + n)) :
    ((Polynomial.sylvester f g m n) i j).natDegree ≤
      (Fin.addCases (fun _ => dg) (fun _ => df) j : ℕ) := by
  induction j using Fin.addCases with
  | left j =>
    simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
    split_ifs
    · exact hg _
    · simp
  | right j =>
    simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
    split_ifs
    · exact hf _
    · simp

/-- Degree bound for the Sylvester resultant of two bivariate polynomials: with formal
inner degrees `(m, n)` and outer coefficient bounds `(df, dg)`,
`deg_Z Res ≤ m·dg + n·df`. -/
theorem natDegree_resultant_le (f g : F[X][Y]) (m n df dg : ℕ)
    (hf : ∀ k, (f.coeff k).natDegree ≤ df) (hg : ∀ k, (g.coeff k).natDegree ≤ dg) :
    (Polynomial.resultant f g m n).natDegree ≤ m * dg + n * df := by
  rw [Polynomial.resultant]
  refine le_trans (natDegree_det_le _ (Fin.addCases (fun _ => dg) (fun _ => df))
    (fun i j => natDegree_sylvester_entry_le f g m n df dg hf hg i j)) ?_
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]
  omega

/-- **The crux row-operation lemma.** If on the line `z` we have
`g(·,z) = f(·,z)·q` with the Cramer degree bound `deg q + m ≤ n`, then
`(Z − z)^m ∣ Res(f, g)` (formal degrees `(m, n)`).

Proof: lift `q` to `q̃` with constant coefficients; `g' := g − f·q̃` specializes to `0`
at `z`, so every coefficient of `g'` is divisible by `Z − z`. The row operation
`Res(f, g' + f·q̃) = Res(f, g')` is exactly `Polynomial.resultant_add_mul_right`, legal
because `deg q̃ + m ≤ n` — the Cramer bound. Multilinearity in the `m` `g`-columns
(`Polynomial.resultant_C_mul_right`) then extracts `(Z − z)^m`. -/
theorem pow_X_sub_C_dvd_resultant (f g : F[X][Y]) (m n : ℕ) (z : F) (q : Polynomial F)
    (hfm : f.natDegree ≤ m) (hqm : q.natDegree + m ≤ n)
    (hline : g.map (evalRingHom z) = f.map (evalRingHom z) * q) :
    ((X : Polynomial F) - C z) ^ m ∣ Polynomial.resultant f g m n := by
  classical
  set qt : F[X][Y] := q.map (Polynomial.C : F →+* Polynomial F) with hqt
  have hqt_deg : qt.natDegree ≤ q.natDegree := Polynomial.natDegree_map_le
  have hqt_map : qt.map (evalRingHom z) = q := by
    rw [hqt, Polynomial.map_map]
    have hcomp : (evalRingHom z).comp (Polynomial.C (R := F)) = RingHom.id F := by
      ext x; simp
    rw [hcomp, Polynomial.map_id]
  set g' : F[X][Y] := g - f * qt with hg'
  have hkey : ∀ k, ((X : Polynomial F) - C z) ∣ g'.coeff k := by
    intro k
    rw [Polynomial.dvd_iff_isRoot]
    have hmap : g'.map (evalRingHom z) = 0 := by
      rw [hg', Polynomial.map_sub, Polynomial.map_mul, hqt_map, hline, sub_self]
    have hcoeff := congrArg (fun p => p.coeff k) hmap
    simpa only [Polynomial.coeff_map, Polynomial.coeff_zero, Polynomial.IsRoot,
      coe_evalRingHom] using hcoeff
  obtain ⟨h, hh⟩ := (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr hkey
  have hres : Polynomial.resultant f g m n = Polynomial.resultant f g' m n := by
    have hgsplit : g = g' + f * qt := by rw [hg']; ring
    rw [hgsplit]
    exact Polynomial.resultant_add_mul_right _ _ _ _ _ (by omega) hfm
  rw [hres, hh, Polynomial.resultant_C_mul_right]
  exact dvd_mul_right _ _

section CoprimalityTransfer

open scoped nonZeroDivisors

/-- Gauss-lemma transfer: a UFD-coprime (no common factor) pair stays Bezout-coprime
over the fraction field. -/
theorem isCoprime_map_of_isRelPrime {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    {f g : R[X]} (hf : f ≠ 0) (hrel : IsRelPrime f g) :
    IsCoprime (f.map (algebraMap R K)) (g.map (algebraMap R K)) := by
  classical
  by_contra hnc
  set φ := algebraMap R K with hφ
  have hinj : Function.Injective φ := IsFractionRing.injective R K
  have hf' : f.map φ ≠ 0 := fun h => hf ((Polynomial.map_eq_zero_iff hinj).mp h)
  set d := EuclideanDomain.gcd (f.map φ) (g.map φ) with hd
  have hdu : ¬IsUnit d := by
    intro hu
    apply hnc
    obtain ⟨w, hw⟩ := hu.exists_left_inv
    refine ⟨w * EuclideanDomain.gcdA (f.map φ) (g.map φ),
      w * EuclideanDomain.gcdB (f.map φ) (g.map φ), ?_⟩
    have hbez := EuclideanDomain.gcd_eq_gcd_ab (f.map φ) (g.map φ)
    rw [← hd] at hbez
    have hw' : w * d = 1 := hw
    rw [hbez] at hw'
    linear_combination hw'
  have hd0 : d ≠ 0 := by
    rw [hd, Ne, EuclideanDomain.gcd_eq_zero_iff]
    tauto
  obtain ⟨p, hpirr, hpd⟩ := WfDvdMonoid.exists_irreducible_factor hdu hd0
  have hpf : p ∣ f.map φ := hpd.trans (EuclideanDomain.gcd_dvd_left _ _)
  have hpg : p ∣ g.map φ := hpd.trans (EuclideanDomain.gcd_dvd_right _ _)
  have hp0 : p ≠ 0 := hpirr.ne_zero
  letI : NormalizedGCDMonoid R := Nonempty.some inferInstance
  set p₁ := IsLocalization.integerNormalization R⁰ p with hp₁
  obtain ⟨c, hcmem, hc⟩ := IsLocalization.integerNormalization_spec R⁰ p
  have hp₁0 : p₁ ≠ 0 := by
    rw [hp₁, Ne, IsFractionRing.integerNormalization_eq_zero_iff]
    exact hp0
  have hcne : φ c ≠ 0 := fun h =>
    nonZeroDivisors.ne_zero hcmem ((injective_iff_map_eq_zero φ).mp hinj c h)
  have hcontne : φ p₁.content ≠ 0 := fun h =>
    hp₁0 (Polynomial.content_eq_zero_iff.mp
      ((injective_iff_map_eq_zero φ).mp hinj p₁.content h))
  have hc' : p₁.map φ = Polynomial.C (φ c) * p := by
    rw [← hp₁] at hc
    rw [hc, Algebra.smul_def, Polynomial.algebraMap_apply]
  have hsplit : Polynomial.C (φ p₁.content) * p₁.primPart.map φ = Polynomial.C (φ c) * p := by
    have h1 := congrArg (Polynomial.map φ) (Polynomial.eq_C_content_mul_primPart p₁)
    rw [Polynomial.map_mul, Polynomial.map_C] at h1
    rw [← h1, hc']
  -- p₁.primPart.map φ divides both maps (up to the unit constants).
  have hppdvd : ∀ w : R[X], p ∣ w.map φ → p₁.primPart.map φ ∣ w.map φ := by
    intro w hw
    have h2 : Polynomial.C (φ p₁.content) * p₁.primPart.map φ ∣
        Polynomial.C (φ c) * w.map φ := by
      rw [hsplit]
      exact mul_dvd_mul_left _ hw
    have h3 : p₁.primPart.map φ ∣ Polynomial.C (φ c) * w.map φ :=
      dvd_trans (Dvd.intro_left _ rfl) h2
    rwa [(Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hcne)).dvd_mul_left] at h3
  -- push the divisibility down to R[X] via Gauss's lemma
  have hdown : ∀ w : R[X], w ≠ 0 → p ∣ w.map φ → p₁.primPart ∣ w := by
    intro w hw0 hw
    have hwcont : φ w.content ≠ 0 := fun h =>
      hw0 (Polynomial.content_eq_zero_iff.mp
        ((injective_iff_map_eq_zero φ).mp hinj w.content h))
    have h4 : p₁.primPart.map φ ∣ w.primPart.map φ := by
      have h5 := hppdvd w hw
      have h6 := congrArg (Polynomial.map φ) (Polynomial.eq_C_content_mul_primPart w)
      rw [Polynomial.map_mul, Polynomial.map_C] at h6
      rw [h6] at h5
      rwa [(Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hwcont)).dvd_mul_left] at h5
    have h7 : p₁.primPart ∣ w.primPart :=
      Polynomial.IsPrimitive.dvd_of_fraction_map_dvd_fraction_map
        (Polynomial.isPrimitive_primPart p₁) h4
    exact h7.trans (Dvd.intro_left _ (Polynomial.eq_C_content_mul_primPart w).symm)
  have hg0 : g ≠ 0 ∨ p₁.primPart ∣ g := by
    rcases eq_or_ne g 0 with rfl | hg
    · exact Or.inr (dvd_zero _)
    · exact Or.inl hg
  have hdvdf : p₁.primPart ∣ f := hdown f hf hpf
  have hdvdg : p₁.primPart ∣ g := by
    rcases hg0 with hg | hg
    · exact hdown g hg hpg
    · exact hg
  have hunit : IsUnit p₁.primPart := hrel hdvdf hdvdg
  -- transfer the unit back up to p, contradicting irreducibility
  have hunit' : IsUnit (p₁.primPart.map φ) := by
    have := hunit.map (Polynomial.mapRingHom φ)
    simpa using this
  have hCp : IsUnit (Polynomial.C (φ c) * p) := by
    rw [← hsplit]
    exact (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hcontne)).mul hunit'
  exact hpirr.not_isUnit (IsUnit.mul_iff.mp hCp).2

end CoprimalityTransfer

/-- Nonvanishing of the Sylvester resultant of a UFD-coprime pair, with the exact
formal degree on the `f`-side and arbitrary formal slack `n ≥ deg g` on the `g`-side. -/
theorem resultant_ne_zero_of_isRelPrime (f g : F[X][Y]) (hf : f ≠ 0)
    (hcop : IsRelPrime f g) (n : ℕ) (hn : g.natDegree ≤ n) :
    Polynomial.resultant f g f.natDegree n ≠ 0 := by
  classical
  set K := FractionRing (Polynomial F) with hK
  set φ : Polynomial F →+* K := algebraMap (Polynomial F) K with hφ
  have hinj : Function.Injective φ := IsFractionRing.injective _ _
  have hcopK : IsCoprime (f.map φ) (g.map φ) := isCoprime_map_of_isRelPrime K hf hcop
  have hfd : (f.map φ).natDegree = f.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hinj f
  have hgd : (g.map φ).natDegree = g.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hinj g
  have hf' : f.map φ ≠ 0 := fun h => hf ((Polynomial.map_eq_zero_iff hinj).mp h)
  have hlc : φ f.leadingCoeff ≠ 0 := fun h =>
    hf (Polynomial.leadingCoeff_eq_zero.mp ((injective_iff_map_eq_zero φ).mp hinj _ h))
  have hK0 : Polynomial.resultant (f.map φ) (g.map φ) f.natDegree n ≠ 0 := by
    have hsplit : n = (g.map φ).natDegree + (n - g.natDegree) := by rw [hgd]; omega
    rw [hsplit, Polynomial.resultant_add_right_deg _ _ _ _ _ le_rfl]
    apply mul_ne_zero
    · have hcf : (f.map φ).coeff f.natDegree = φ f.leadingCoeff := by
        rw [Polynomial.coeff_map, Polynomial.leadingCoeff]
      rw [hcf]
      exact pow_ne_zero _ hlc
    · have hres : Polynomial.resultant (f.map φ) (g.map φ) f.natDegree (g.map φ).natDegree
          = Polynomial.resultant (f.map φ) (g.map φ) := by rw [hfd]
      rw [hres]
      intro h0
      rw [Polynomial.resultant_eq_zero_iff] at h0
      exact h0.2 hcopK
  intro h0
  apply hK0
  rw [Polynomial.resultant_map_map, h0, map_zero]

/-- Transfer of UFD-coprimality across the variable swap. -/
theorem isRelPrime_swap {A B : F[X][Y]} (h : IsRelPrime A B) :
    IsRelPrime (Polynomial.Bivariate.swap A) (Polynomial.Bivariate.swap B) := by
  intro d hdA hdB
  have h1 : Polynomial.Bivariate.swap d ∣ A := by
    have := map_dvd (Polynomial.Bivariate.swap (R := F)) hdA
    rwa [Polynomial.Bivariate.swap_swap_apply] at this
  have h2 : Polynomial.Bivariate.swap d ∣ B := by
    have := map_dvd (Polynomial.Bivariate.swap (R := F)) hdB
    rwa [Polynomial.Bivariate.swap_swap_apply] at this
  have hu := h h1 h2
  have := hu.map (Polynomial.Bivariate.swap (R := F))
  rwa [Polynomial.Bivariate.swap_swap_apply] at this

/-- **The horizontal-line counting inequality.** For a coprime nonzero pair with
`deg_X A ≤ a_X ≤ b_X`, `deg_X B ≤ b_X`, `deg_Z B ≤ b_Z`, and divisibility with
Cramer-bounded quotients on the lines of `S`:
`deg_X A · |S| ≤ deg_X A · b_Z + b_X · deg_Z A`. -/
theorem count_horizontal_lines (A B : F[X][Y]) (hA : A ≠ 0)
    (hcop : IsRelPrime A B) (aX bX bZ : ℕ) (hAX : sdeg A ≤ aX) (haXbX : aX ≤ bX)
    (hBX : sdeg B ≤ bX) (hBZ : B.natDegree ≤ bZ) (S : Finset F)
    (hdiv : ∀ z ∈ S, ∃ q : Polynomial F,
      B.eval (C z) = A.eval (C z) * q ∧ q.natDegree ≤ bX - aX) :
    sdeg A * S.card ≤ sdeg A * bZ + bX * A.natDegree := by
  classical
  have hcop' : IsRelPrime (Polynomial.Bivariate.swap A) (Polynomial.Bivariate.swap B) :=
    isRelPrime_swap hcop
  have hR0 : Polynomial.resultant (Polynomial.Bivariate.swap A)
      (Polynomial.Bivariate.swap B) (sdeg A) bX ≠ 0 := by
    have h := resultant_ne_zero_of_isRelPrime (Polynomial.Bivariate.swap A)
      (Polynomial.Bivariate.swap B) (swap_ne_zero hA) hcop' bX hBX
    exact h
  have hdvd : ∀ z ∈ S, ((X : Polynomial F) - C z) ^ (sdeg A) ∣
      Polynomial.resultant (Polynomial.Bivariate.swap A)
        (Polynomial.Bivariate.swap B) (sdeg A) bX := by
    intro z hz
    obtain ⟨q, hq, hqd⟩ := hdiv z hz
    refine pow_X_sub_C_dvd_resultant _ _ _ _ z q le_rfl (by omega) ?_
    rw [swap_map_evalRingHom, swap_map_evalRingHom, hq]
  have hprod : (∏ z ∈ S, ((X : Polynomial F) - C z) ^ (sdeg A)) ∣
      Polynomial.resultant (Polynomial.Bivariate.swap A)
        (Polynomial.Bivariate.swap B) (sdeg A) bX := by
    apply Finset.prod_dvd_of_coprime
    · intro z hz w hw hzw
      exact ((Polynomial.pairwise_coprime_X_sub_C (Function.injective_id) hzw).pow :)
    · exact hdvd
  have hprodcard : (∏ z ∈ S, ((X : Polynomial F) - C z) ^ (sdeg A)).natDegree
      = sdeg A * S.card := by
    rw [Polynomial.natDegree_prod _ _ (fun z _ => pow_ne_zero _ (Polynomial.X_sub_C_ne_zero z))]
    have : ∀ z ∈ S, (((X : Polynomial F) - C z) ^ (sdeg A)).natDegree = sdeg A := by
      intro z _
      rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
    rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul, mul_comm]
  have hle := Polynomial.natDegree_le_of_dvd hprod hR0
  rw [hprodcard] at hle
  refine le_trans hle ?_
  refine natDegree_resultant_le _ _ _ _ A.natDegree bZ ?_ ?_
  · intro k
    have h := coeff_natDegree_le_sdeg (Polynomial.Bivariate.swap A) k
    rwa [sdeg_swap] at h
  · intro k
    have h := coeff_natDegree_le_sdeg (Polynomial.Bivariate.swap B) k
    rw [sdeg_swap] at h
    exact le_trans h hBZ

/-! ## The coprime-core counting endgame -/

/-- The pure-arithmetic endgame: the two counting inequalities against the budget
force the first degree to vanish. -/
private theorem budget_aux {αX αZ bX bZ nX nZ : ℕ}
    (h1 : αX * nZ ≤ αX * bZ + bX * αZ) (h2 : αZ * nX ≤ αZ * bX + bZ * αX)
    (hbX : bX < nX) (hbZ : bZ < nZ)
    (hbudget : bX * nZ + bZ * nX < nX * nZ) : αX = 0 := by
  by_contra hx
  have hx' : 0 < αX := Nat.pos_of_ne_zero hx
  rcases Nat.eq_zero_or_pos αZ with hz | hz
  · subst hz
    simp only [mul_zero, add_zero] at h1
    have := Nat.le_of_mul_le_mul_left h1 hx'
    omega
  · have e1 : αX * (nZ - bZ) ≤ bX * αZ := by
      zify [hbZ.le]
      zify at h1
      nlinarith [h1]
    have e2 : αZ * (nX - bX) ≤ bZ * αX := by
      zify [hbX.le]
      zify at h2
      nlinarith [h2]
    have e3 := Nat.mul_le_mul e1 e2
    have e4 : (nZ - bZ) * (nX - bX) ≤ bX * bZ := by
      have hpos : 0 < αX * αZ := Nat.mul_pos hx' hz
      apply Nat.le_of_mul_le_mul_left _ hpos
      calc (αX * αZ) * ((nZ - bZ) * (nX - bX))
          = (αX * (nZ - bZ)) * (αZ * (nX - bX)) := by ring
        _ ≤ (bX * αZ) * (bZ * αX) := e3
        _ = (αX * αZ) * (bX * bZ) := by ring
    zify [hbX.le, hbZ.le] at e4
    zify at hbudget
    nlinarith [e4, hbudget]

/-- **The coprime core.** A UFD-coprime nonzero pair satisfying the line-divisibility
hypotheses (with Cramer quotient bounds) and the degree budget has constant `A`. -/
theorem coprime_core (A B : F[X][Y]) (hA : A ≠ 0) (hcop : IsRelPrime A B)
    (aX aZ bX bZ : ℕ) (S_X S_Z : Finset F)
    (hAX : sdeg A ≤ aX) (hAZ : A.natDegree ≤ aZ)
    (hBX : sdeg B ≤ bX) (hBZ : B.natDegree ≤ bZ)
    (haXbX : aX ≤ bX) (haZbZ : aZ ≤ bZ)
    (hvert : ∀ x ∈ S_X, ∃ q : Polynomial F,
      B.map (evalRingHom x) = A.map (evalRingHom x) * q ∧ q.natDegree ≤ bZ - aZ)
    (hhoriz : ∀ z ∈ S_Z, ∃ q : Polynomial F,
      B.eval (C z) = A.eval (C z) * q ∧ q.natDegree ≤ bX - aX)
    (hbudget : bX * S_Z.card + bZ * S_X.card < S_X.card * S_Z.card) :
    sdeg A = 0 ∧ A.natDegree = 0 := by
  have h0 : 0 < S_X.card * S_Z.card := lt_of_le_of_lt (Nat.zero_le _) hbudget
  have hbXnX : bX < S_X.card := by
    by_contra hcon
    rw [not_lt] at hcon
    have hmul : S_X.card * S_Z.card ≤ bX * S_Z.card := Nat.mul_le_mul_right _ hcon
    have := Nat.zero_le (bZ * S_X.card)
    omega
  have hbZnZ : bZ < S_Z.card := by
    by_contra hcon
    rw [not_lt] at hcon
    have hmul : S_X.card * S_Z.card ≤ S_X.card * bZ := Nat.mul_le_mul_left _ hcon
    have hcomm : S_X.card * bZ = bZ * S_X.card := Nat.mul_comm _ _
    have := Nat.zero_le (bX * S_Z.card)
    omega
  have h1 := count_horizontal_lines A B hA hcop aX bX bZ hAX haXbX hBX hBZ S_Z hhoriz
  have h2 : A.natDegree * S_X.card ≤ A.natDegree * bX + bZ * sdeg A := by
    have hvert' : ∀ x ∈ S_X, ∃ q : Polynomial F,
        (Polynomial.Bivariate.swap B).eval (C x)
          = (Polynomial.Bivariate.swap A).eval (C x) * q ∧ q.natDegree ≤ bZ - aZ := by
      intro x hx
      obtain ⟨q, hq, hqd⟩ := hvert x hx
      refine ⟨q, ?_, hqd⟩
      rw [← map_evalRingHom_eq_eval_swap, ← map_evalRingHom_eq_eval_swap, hq]
    have h := count_horizontal_lines (Polynomial.Bivariate.swap A)
      (Polynomial.Bivariate.swap B) (swap_ne_zero hA)
      (isRelPrime_swap hcop) aZ bZ bX
      (by rw [sdeg_swap]; exact hAZ) haZbZ
      (by rw [sdeg_swap]; exact hBZ)
      (by rw [← sdeg_def]; exact hBX) S_X hvert'
    rw [sdeg_swap, ← sdeg_def] at h
    exact h
  constructor
  · exact budget_aux h1 h2 hbXnX hbZnZ hbudget
  · apply budget_aux h2 h1 hbZnZ hbXnX
    have hc1 : bZ * S_X.card + bX * S_Z.card = bX * S_Z.card + bZ * S_X.card :=
      Nat.add_comm _ _
    have hc2 : S_Z.card * S_X.card = S_X.card * S_Z.card := Nat.mul_comm _ _
    omega

/-! ## Quotient degree bounds from one good line -/

/-- If `A·Q` satisfies the horizontal-line divisibility hypotheses with quotient degree
bound `d` on more lines than `deg_Z (A·Q)`, then `deg_X Q ≤ d`. -/
theorem sdeg_quotient_le (A Q : F[X][Y]) (hA : A ≠ 0) (hQ : Q ≠ 0)
    (S : Finset F) (d : ℕ)
    (hdiv : ∀ z ∈ S, ∃ q : Polynomial F,
      (A * Q).eval (C z) = A.eval (C z) * q ∧ q.natDegree ≤ d)
    (hcard : (A * Q).natDegree < S.card) :
    sdeg Q ≤ d := by
  classical
  set c : Polynomial F := (Polynomial.Bivariate.swap Q).leadingCoeff with hc
  have hc0 : c ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr (swap_ne_zero hQ)
  have hcdeg : c.natDegree ≤ Q.natDegree := by
    have h1 := coeff_natDegree_le_sdeg (Polynomial.Bivariate.swap Q)
      (Polynomial.Bivariate.swap Q).natDegree
    rw [sdeg_swap] at h1
    exact h1
  set bad1 := S.filter (fun z => A.eval (C z) = 0) with hbad1
  set bad2 := S.filter (fun z => c.eval z = 0) with hbad2
  have hb1 : bad1.card ≤ A.natDegree := card_filter_horizontal_zero_le S hA
  have hb2 : bad2.card ≤ Q.natDegree := le_trans (card_filter_eval_zero_le S hc0) hcdeg
  have hAQdeg : (A * Q).natDegree = A.natDegree + Q.natDegree :=
    Polynomial.natDegree_mul hA hQ
  have hex : ∃ z ∈ S, z ∉ bad1 ∪ bad2 := by
    rw [← Finset.not_subset]
    intro hsub
    have hle1 := Finset.card_le_card hsub
    have hle2 := Finset.card_union_le bad1 bad2
    omega
  obtain ⟨z, hzS, hzbad⟩ := hex
  rw [Finset.mem_union, not_or] at hzbad
  obtain ⟨hz1, hz2⟩ := hzbad
  have hz1' : A.eval (C z) ≠ 0 := fun h => hz1 (Finset.mem_filter.mpr ⟨hzS, h⟩)
  have hz2' : c.eval z ≠ 0 := fun h => hz2 (Finset.mem_filter.mpr ⟨hzS, h⟩)
  obtain ⟨q, hq, hqd⟩ := hdiv z hzS
  have hQz : Q.eval (C z) = q := by
    apply mul_left_cancel₀ hz1'
    rw [← Polynomial.eval_mul]
    exact hq
  have hQline : (Q.eval (C z)).natDegree = sdeg Q := by
    rw [← swap_map_evalRingHom, sdeg_def]
    exact Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hz2'
  rw [← hQline, hQz]
  exact hqd

/-! ## The budget survives the gcd reduction -/

private theorem budget_shrink {bX bZ gX gZ nX nZ u v : ℕ}
    (hgX : gX ≤ bX) (hgZ : gZ ≤ bZ) (hbX : bX < nX) (hbZ : bZ < nZ)
    (hu : nX - gX ≤ u) (hv : nZ - gZ ≤ v)
    (hbudget : bX * nZ + bZ * nX < nX * nZ) :
    (bX - gX) * v + (bZ - gZ) * u < u * v := by
  have key1 : (bX - gX) * nX ≤ bX * (nX - gX) := by
    zify [hgX, hgX.trans hbX.le]
    nlinarith [hbX.le]
  have key2 : (bZ - gZ) * nZ ≤ bZ * (nZ - gZ) := by
    zify [hgZ, hgZ.trans hbZ.le]
    nlinarith [hbZ.le]
  have hu0 : 0 < u := by omega
  have hv0 : 0 < v := by omega
  have main : ((bX - gX) * v + (bZ - gZ) * u) * (nX * nZ) < (u * v) * (nX * nZ) := by
    calc ((bX - gX) * v + (bZ - gZ) * u) * (nX * nZ)
        = ((bX - gX) * nX) * (v * nZ) + ((bZ - gZ) * nZ) * (u * nX) := by ring
      _ ≤ (bX * (nX - gX)) * (v * nZ) + (bZ * (nZ - gZ)) * (u * nX) := by
          gcongr
      _ ≤ (bX * u) * (v * nZ) + (bZ * v) * (u * nX) := by
          gcongr
      _ = (u * v) * (bX * nZ + bZ * nX) := by ring
      _ < (u * v) * (nX * nZ) := by
          exact mul_lt_mul_of_pos_left hbudget (Nat.mul_pos hu0 hv0)
  exact lt_of_mul_lt_mul_right main (Nat.zero_le _)

/-- A bivariate polynomial of vanishing outer and inner degree is a constant. -/
theorem eq_CC_of_deg_zero (p : F[X][Y]) (h1 : sdeg p = 0) (h2 : p.natDegree = 0) :
    ∃ a : F, p = Polynomial.CC a := by
  obtain ⟨pa, hpa⟩ := Polynomial.natDegree_eq_zero.mp h2
  have hsd : sdeg (Polynomial.C pa : F[X][Y]) = pa.natDegree := by
    rw [sdeg_def, Polynomial.Bivariate.swap_C]
    exact Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective pa
  rw [hpa, h1] at hsd
  obtain ⟨a, ha⟩ := Polynomial.natDegree_eq_zero.mp hsd.symm
  exact ⟨a, by rw [← hpa, ← ha]⟩

/-! ## L3.2 — the main theorem -/

/-- **The Polishchuk–Spielman lemma** (BCIKS20 Lemma 4.3, rev.3 / Cramer–Nardi-fixed form).

Let `A, B ∈ F[X][Z]` with formal degree bounds `deg_X A ≤ a_X`, `deg_Z A ≤ a_Z`,
`deg_X B ≤ b_X`, `deg_Z B ≤ b_Z` (`a_X ≤ b_X`, `a_Z ≤ b_Z`). Suppose
* on each of the `n_X := |S_X|` vertical lines `x ∈ S_X`:
  `B(x,Z) = A(x,Z)·q_x` with `deg q_x ≤ b_Z − a_Z`;
* on each of the `n_Z := |S_Z|` horizontal lines `z ∈ S_Z`:
  `B(X,z) = A(X,z)·q_z` with `deg q_z ≤ b_X − a_X`;
* the budget `b_X·n_Z + b_Z·n_X < n_X·n_Z` (i.e. `b_X/n_X + b_Z/n_Z < 1`).

Then `A ∣ B` in `F[X][Z]`, with quotient degrees bounded by `b_X − a_X` and `b_Z − a_Z`. -/
theorem polishchuk_spielman (A B : F[X][Y]) (aX aZ bX bZ : ℕ) (S_X S_Z : Finset F)
    (hAX : sdeg A ≤ aX) (hAZ : A.natDegree ≤ aZ)
    (hBX : sdeg B ≤ bX) (hBZ : B.natDegree ≤ bZ)
    (haXbX : aX ≤ bX) (haZbZ : aZ ≤ bZ)
    (hvert : ∀ x ∈ S_X, ∃ q : Polynomial F,
      B.map (evalRingHom x) = A.map (evalRingHom x) * q ∧ q.natDegree ≤ bZ - aZ)
    (hhoriz : ∀ z ∈ S_Z, ∃ q : Polynomial F,
      B.eval (C z) = A.eval (C z) * q ∧ q.natDegree ≤ bX - aX)
    (hbudget : bX * S_Z.card + bZ * S_X.card < S_X.card * S_Z.card) :
    ∃ Q : F[X][Y], B = A * Q ∧ sdeg Q ≤ bX - aX ∧ Q.natDegree ≤ bZ - aZ := by
  classical
  have h0 : 0 < S_X.card * S_Z.card := lt_of_le_of_lt (Nat.zero_le _) hbudget
  have hbXnX : bX < S_X.card := by
    by_contra hcon
    rw [not_lt] at hcon
    have hmul : S_X.card * S_Z.card ≤ bX * S_Z.card := Nat.mul_le_mul_right _ hcon
    have := Nat.zero_le (bZ * S_X.card)
    omega
  have hbZnZ : bZ < S_Z.card := by
    by_contra hcon
    rw [not_lt] at hcon
    have hmul : S_X.card * S_Z.card ≤ S_X.card * bZ := Nat.mul_le_mul_left _ hcon
    have hcomm : S_X.card * bZ = bZ * S_X.card := Nat.mul_comm _ _
    have := Nat.zero_le (bX * S_Z.card)
    omega
  rcases eq_or_ne B 0 with rfl | hB
  · exact ⟨0, by ring, by simp, by simp⟩
  rcases eq_or_ne A 0 with rfl | hA
  · exfalso
    have hall : ∀ x ∈ S_X, B.map (evalRingHom x) = 0 := by
      intro x hx
      obtain ⟨q, hq, -⟩ := hvert x hx
      simpa using hq
    have hcount : S_X.card ≤ sdeg B := by
      have h := card_filter_vertical_zero_le S_X hB
      rwa [Finset.filter_true_of_mem hall] at h
    omega
  -- split off the gcd
  letI : GCDMonoid (F[X][Y]) := UniqueFactorizationMonoid.toGCDMonoid _
  set G := gcd A B with hG
  have hGA : G ∣ A := gcd_dvd_left A B
  have hGB : G ∣ B := gcd_dvd_right A B
  have hG0 : G ≠ 0 := by
    intro h
    exact hA (zero_dvd_iff.mp (h ▸ hGA))
  obtain ⟨A₁, hA₁⟩ := hGA
  obtain ⟨B₁, hB₁⟩ := hGB
  have hA₁0 : A₁ ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hA₁
    exact hA hA₁
  have hB₁0 : B₁ ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hB₁
    exact hB hB₁
  have hrel : IsRelPrime A₁ B₁ := by
    intro d hd1 hd2
    have h1 : G * d ∣ A := by rw [hA₁]; exact mul_dvd_mul_left G hd1
    have h2 : G * d ∣ B := by rw [hB₁]; exact mul_dvd_mul_left G hd2
    have hdvd : G * d ∣ G := dvd_gcd h1 h2
    have hd1' : G * d ∣ G * 1 := by simpa using hdvd
    exact isUnit_of_dvd_one ((mul_dvd_mul_iff_left hG0).mp hd1')
  have hsA : sdeg A = sdeg G + sdeg A₁ := by rw [hA₁]; exact sdeg_mul hG0 hA₁0
  have hnA : A.natDegree = G.natDegree + A₁.natDegree := by
    rw [hA₁]; exact Polynomial.natDegree_mul hG0 hA₁0
  have hsB : sdeg B = sdeg G + sdeg B₁ := by rw [hB₁]; exact sdeg_mul hG0 hB₁0
  have hnB : B.natDegree = G.natDegree + B₁.natDegree := by
    rw [hB₁]; exact Polynomial.natDegree_mul hG0 hB₁0
  have hgXbX : sdeg G ≤ bX := by omega
  have hgZbZ : G.natDegree ≤ bZ := by omega
  -- prune the lines where G vanishes identically
  set badX := S_X.filter (fun x => G.map (evalRingHom x) = 0) with hbadX
  set SX' := S_X \ badX with hSX'
  have hbadX_card : badX.card ≤ sdeg G := card_filter_vertical_zero_le S_X hG0
  have hSX'_card : S_X.card - sdeg G ≤ SX'.card := by
    have h2 : SX'.card = S_X.card - (badX ∩ S_X).card := by
      rw [hSX', Finset.card_sdiff]
    have h3 : (badX ∩ S_X).card ≤ badX.card := Finset.card_le_card Finset.inter_subset_left
    omega
  set badZ := S_Z.filter (fun z => G.eval (C z) = 0) with hbadZ
  set SZ' := S_Z \ badZ with hSZ'
  have hbadZ_card : badZ.card ≤ G.natDegree := card_filter_horizontal_zero_le S_Z hG0
  have hSZ'_card : S_Z.card - G.natDegree ≤ SZ'.card := by
    have h2 : SZ'.card = S_Z.card - (badZ ∩ S_Z).card := by
      rw [hSZ', Finset.card_sdiff]
    have h3 : (badZ ∩ S_Z).card ≤ badZ.card := Finset.card_le_card Finset.inter_subset_left
    omega
  -- transformed line hypotheses for the coprime pair
  have hvert' : ∀ x ∈ SX', ∃ q : Polynomial F,
      B₁.map (evalRingHom x) = A₁.map (evalRingHom x) * q ∧
        q.natDegree ≤ (bZ - G.natDegree) - (aZ - G.natDegree) := by
    intro x hx
    have hxS : x ∈ S_X := (Finset.mem_sdiff.mp hx).1
    have hxg : G.map (evalRingHom x) ≠ 0 := by
      have hnot := (Finset.mem_sdiff.mp hx).2
      rw [hbadX, Finset.mem_filter, not_and] at hnot
      exact hnot hxS
    obtain ⟨q, hq, hqd⟩ := hvert x hxS
    refine ⟨q, ?_, ?_⟩
    · apply mul_left_cancel₀ hxg
      rw [← mul_assoc, ← Polynomial.map_mul, ← Polynomial.map_mul, ← hA₁, ← hB₁, hq]
    · have hgZaZ : G.natDegree ≤ aZ := by omega
      omega
  have hhoriz' : ∀ z ∈ SZ', ∃ q : Polynomial F,
      B₁.eval (C z) = A₁.eval (C z) * q ∧
        q.natDegree ≤ (bX - sdeg G) - (aX - sdeg G) := by
    intro z hz
    have hzS : z ∈ S_Z := (Finset.mem_sdiff.mp hz).1
    have hzg : G.eval (C z) ≠ 0 := by
      have hnot := (Finset.mem_sdiff.mp hz).2
      rw [hbadZ, Finset.mem_filter, not_and] at hnot
      exact hnot hzS
    obtain ⟨q, hq, hqd⟩ := hhoriz z hzS
    refine ⟨q, ?_, ?_⟩
    · apply mul_left_cancel₀ hzg
      rw [← mul_assoc, ← Polynomial.eval_mul, ← Polynomial.eval_mul, ← hA₁, ← hB₁, hq]
    · have hgXaX : sdeg G ≤ aX := by omega
      omega
  -- the budget survives the reduction
  have hbud' : (bX - sdeg G) * SZ'.card + (bZ - G.natDegree) * SX'.card
      < SX'.card * SZ'.card :=
    budget_shrink hgXbX hgZbZ hbXnX hbZnZ hSX'_card hSZ'_card hbudget
  -- coprime core: A₁ is constant
  have hcore := coprime_core A₁ B₁ hA₁0 hrel
    (aX - sdeg G) (aZ - G.natDegree) (bX - sdeg G) (bZ - G.natDegree) SX' SZ'
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    hvert' hhoriz' hbud'
  obtain ⟨hs0, hn0⟩ := hcore
  obtain ⟨a, ha⟩ := eq_CC_of_deg_zero A₁ hs0 hn0
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hA₁0
    rw [ha]
    simp
  -- the quotient
  set Qq : F[X][Y] := Polynomial.CC a⁻¹ * B₁ with hQq
  have hCCunit : (Polynomial.CC a : F[X][Y]) * Polynomial.CC a⁻¹ = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ ha0, map_one, map_one]
  have hBeq : B = A * Qq := by
    rw [hB₁, hA₁, ha, hQq]
    calc G * B₁ = G * ((Polynomial.CC a * Polynomial.CC a⁻¹) * B₁) := by
          rw [hCCunit, one_mul]
      _ = G * Polynomial.CC a * (Polynomial.CC a⁻¹ * B₁) := by ring
  have hQq0 : Qq ≠ 0 := by
    rw [hQq]
    apply mul_ne_zero _ hB₁0
    simpa using inv_ne_zero ha0
  refine ⟨Qq, hBeq, ?_, ?_⟩
  · -- sdeg Qq ≤ bX - aX from one good horizontal line
    apply sdeg_quotient_le A Qq hA hQq0 S_Z (bX - aX)
    · intro z hz
      obtain ⟨q, hq, hqd⟩ := hhoriz z hz
      exact ⟨q, by rw [← hBeq]; exact hq, hqd⟩
    · rw [← hBeq]
      omega
  · -- natDegree Qq ≤ bZ - aZ from one good vertical line, via swap
    have hswap := sdeg_quotient_le (Polynomial.Bivariate.swap A)
      (Polynomial.Bivariate.swap Qq) (swap_ne_zero hA) (swap_ne_zero hQq0) S_X (bZ - aZ)
      (by
        intro x hx
        obtain ⟨q, hq, hqd⟩ := hvert x hx
        refine ⟨q, ?_, hqd⟩
        rw [← map_mul, ← map_evalRingHom_eq_eval_swap, ← map_evalRingHom_eq_eval_swap,
          ← hBeq, hq])
      (by
        rw [← map_mul]
        have : (Polynomial.Bivariate.swap (A * Qq)).natDegree = sdeg (A * Qq) := rfl
        rw [this, ← hBeq]
        omega)
    rwa [sdeg_swap] at hswap

/-! ## Non-vacuity: the theorem fires on a concrete instance over `ZMod 11`

`A = X` (the inner variable), `B = X·(X + Z)`. Then `deg_X A = 1`, `deg_Z A = 0`,
`deg_X B = 2`, `deg_Z B = 1`; `A(x,Z) = x` divides `B(x,Z) = x·(x+Z)` with quotient
`x + Z` of degree `1 = b_Z − a_Z` on the five vertical lines `x ∈ {1,2,3,4,5}`, and
`A(X,z) = X` divides `B(X,z) = X·(X+z)` with quotient `X + z` of degree `1 = b_X − a_X`
on the three horizontal lines `z ∈ {0,1,2}`. Budget: `2·3 + 1·5 = 11 < 15 = 5·3`. -/

section NonVacuity

instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-- `A = X` (inner variable) over `ZMod 11`. -/
noncomputable def instA : (ZMod 11)[X][Y] := Polynomial.C Polynomial.X

/-- `B = X · (X + Z)` over `ZMod 11`. -/
noncomputable def instB : (ZMod 11)[X][Y] :=
  Polynomial.C Polynomial.X * (Polynomial.C Polynomial.X + Polynomial.X)

/-- The main theorem fires on the concrete instance: every hypothesis is discharged
on actual data, and the conclusion produces the (nontrivial) quotient. -/
theorem polishchuk_spielman_fires :
    ∃ Q : (ZMod 11)[X][Y], instB = instA * Q ∧ sdeg Q ≤ 1 ∧ Q.natDegree ≤ 1 := by
  have hswapA : Polynomial.Bivariate.swap instA = Polynomial.X := by
    rw [instA, Polynomial.Bivariate.swap_C, Polynomial.map_X]
  have hAX : sdeg instA ≤ 1 := by
    rw [sdeg_def, hswapA, Polynomial.natDegree_X]
  have hAZ : instA.natDegree ≤ 0 := by
    rw [instA, Polynomial.natDegree_C]
  have hfactor : sdeg instB ≤ 2 ∧ instB.natDegree ≤ 1 := by
    constructor
    · rw [instB, sdeg_def, map_mul, map_add, Polynomial.Bivariate.swap_C, Polynomial.map_X,
        Polynomial.Bivariate.swap_Y]
      refine le_trans (Polynomial.natDegree_mul_le) ?_
      have h1 : (Polynomial.X + Polynomial.C Polynomial.X :
          (ZMod 11)[X][Y]).natDegree = 1 := Polynomial.natDegree_X_add_C _
      rw [Polynomial.natDegree_X, h1]
    · rw [instB]
      refine le_trans (Polynomial.natDegree_mul_le) ?_
      rw [Polynomial.natDegree_C]
      have h1 : (Polynomial.C Polynomial.X + Polynomial.X :
          (ZMod 11)[X][Y]).natDegree = 1 := by
        rw [add_comm]
        exact Polynomial.natDegree_X_add_C _
      omega
  have hcards : ({1, 2, 3, 4, 5} : Finset (ZMod 11)).card = 5 ∧
      ({0, 1, 2} : Finset (ZMod 11)).card = 3 := by decide
  refine polishchuk_spielman instA instB 1 0 2 1
    ({1, 2, 3, 4, 5} : Finset (ZMod 11)) ({0, 1, 2} : Finset (ZMod 11))
    hAX hAZ hfactor.1 hfactor.2 (by omega) (by omega) ?_ ?_ ?_
  · -- vertical lines: quotient (C X + X).map (evalRingHom x) = C x + X, degree 1
    intro x _
    refine ⟨(Polynomial.C Polynomial.X + Polynomial.X :
      (ZMod 11)[X][Y]).map (evalRingHom x), ?_, ?_⟩
    · rw [instB, instA, Polynomial.map_mul]
    · refine le_trans Polynomial.natDegree_map_le ?_
      have h1 : (Polynomial.C Polynomial.X + Polynomial.X :
          (ZMod 11)[X][Y]).natDegree = 1 := by
        rw [add_comm]
        exact Polynomial.natDegree_X_add_C _
      omega
  · -- horizontal lines: quotient X + C z, degree 1
    intro z _
    refine ⟨Polynomial.X + Polynomial.C z, ?_, ?_⟩
    · rw [instB, instA, Polynomial.eval_mul]
      congr 1
      rw [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
    · rw [Polynomial.natDegree_X_add_C]
  · -- budget: 2·3 + 1·5 = 11 < 15 = 5·3
    rw [hcards.1, hcards.2]
    omega

/-- The concrete quotient really is `X + Z`: the divisibility concluded abstractly by
`polishchuk_spielman_fires` holds by direct computation. -/
example : instB = instA * (Polynomial.C Polynomial.X + Polynomial.X) := rfl

end NonVacuity

/-! ## Axiom hygiene -/

#assert_axioms swap_coeff_coeff
#assert_axioms card_filter_vertical_zero_le
#assert_axioms card_filter_horizontal_zero_le
#assert_axioms leadingCoeff_degree_comparison
#assert_axioms natDegree_resultant_le
#assert_axioms pow_X_sub_C_dvd_resultant
#assert_axioms isCoprime_map_of_isRelPrime
#assert_axioms resultant_ne_zero_of_isRelPrime
#assert_axioms count_horizontal_lines
#assert_axioms coprime_core
#assert_axioms sdeg_quotient_le
#assert_axioms polishchuk_spielman
#assert_axioms polishchuk_spielman_fires

end PS
end Dregg2

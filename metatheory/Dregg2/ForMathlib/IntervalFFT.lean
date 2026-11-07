/-
# `Dregg2.ForMathlib.IntervalFFT` — certified complex interval arithmetic + interval DFT/FFT convolution.

Built on `Dregg2.ForMathlib.CertifiedInterval` (signed rational interval arithmetic with outward rounding).
This file supplies the frequency-domain acceleration named as the remaining lane in
`Dregg2.ForMathlib.IntervalConvolution` §7: a CERTIFIED interval Fourier transform whose output provably
BRACKETS the exact complex DFT, and hence — through the classical complex DFT convolution theorem — brackets the
exact convolution of the input coefficient lists.

## The two ingredients (each genuine, kernel-clean)

1. **Real-valued containment** (`RContains`). The endpoints of a `CertifiedInterval.Interval` are rational, but
   the values a Fourier transform must enclose (roots of unity `exp(2πi k/N)`) are IRRATIONAL reals. So the
   enclosure predicate here is over `ℝ`: `RContains I x := (I.lo:ℝ) ≤ x ≤ (I.hi:ℝ)`. Every `Interval` operation
   (`add`/`neg`/`sub`/`mul`) is re-proved to enclose over `ℝ` (`add_rcontains`, `mul_rcontains`, …); the proofs
   mirror the `ℚ` ones (they use only ordered-field monotonicity) via the order-embedding `ℚ ↪ ℝ`.

2. **Complex intervals** (`CInterval` = a box `⟨re, im⟩` of two real-`Interval`s; `CContains Z z` = the real and
   imaginary parts are each `RContains`ed). Complex `+, -, ·, conj, pow` INHERIT containment directly from the
   real-interval arithmetic — the complex product's four real multiplies are exactly the signed four-corner
   `mul`. `Interval`/`CInterval` are made `AddCommMonoid`s (add = `Interval.add`, zero = `pt 0`), so a Fourier sum
   `∑ j, …` is an honest `Finset.sum` and the enclosure is `csum_ccontains` (a `Finset` induction).

## What is proved (containment is genuine — the interval brackets the exact value)

* `add_rcontains`, `neg_rcontains`, `sub_rcontains`, `mul_rcontains`, `pow_rcontains` — real-valued interval
  arithmetic enclosure (the `ℝ` analog of the `ℚ` `CertifiedInterval` theorems).
* `cadd_ccontains`, `cmul_ccontains`, `cconj_ccontains`, `cpow_ccontains`, `csum_ccontains` — complex interval
  arithmetic enclosure.
* `dftI_contains`, `idftI_contains` — the interval DFT/IDFT (over a certified root table) bracket the exact
  complex `dft`/`idft`.
* `idft_dft_mul` — the exact complex DFT convolution theorem `IDFT(DFT a ⊙ DFT b) = a ⊛ b` (circular),
  kernel-clean from roots-of-unity orthogonality (`Complex.isPrimitiveRoot_exp`, `geom_sum_eq`).
* `fftConvI_contains` — **the centerpiece**: the interval frequency-domain convolution `IDFT(DFT F ⊙ DFT G)`
  brackets the exact circular convolution `cconv a b` of the enclosed coefficient vectors (composing
  `idftI_contains`, `dftI_contains`, and `idft_dft_mul`).
* `fftConv_re_contains_rat` — the bridge back to `CertifiedInterval.Interval` ℚ-`Contains`: when the exact
  convolution value is a real rational (as ML-KEM count convolutions are), the real-part box `Contains` it,
  reconnecting to the `IntervalConvolution` tail machinery (`ivTailSum`, `exactTailFrac_of_interval`).
* Certified roots of unity: `zetaSeed4_contains` — the exact rational seed for `N = 4` (`ζ_4 = i`), giving a
  full certified root table via the `cpow` recurrence (`zetaSeed4_root_table`); `cos_rcontains_of`/
  `sin_rcontains_of` — general Taylor-remainder cos/sin enclosures (from `Real.cos_bound`/`sin_bound` + rational
  angle bounds) for a certified seed at any `N` with `2π/N ≤ 1`.

Kernel-clean: every theorem's axioms ⊆ `{propext, Classical.choice, Quot.sound}`; no `sorry`, no `native_decide`
(verified). §7 assesses the ML-KEM δ instance and names the precisely-scoped remaining kernel-eval cost.
-/
import Mathlib
import Dregg2.ForMathlib.CertifiedInterval

open scoped Real
open Complex

namespace Dregg2.ForMathlib.IntervalFFT

open Dregg2.ForMathlib.CertifiedInterval
open Dregg2.ForMathlib.CertifiedInterval.Interval

/-! ## §1 — real-valued containment for `CertifiedInterval.Interval`

The `CertifiedInterval` enclosure predicate `Contains` is over `ℚ`. A Fourier transform must enclose real
(irrational) values, so we re-express the enclosure over `ℝ` and re-prove the arithmetic enclosure lemmas. -/

/-- Real-valued enclosure: the real number `x` lies in the (rational-endpoint) interval `I`. -/
def RContains (I : Interval) (x : ℝ) : Prop := (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

/-- A rational enclosure gives a real enclosure of the cast. -/
theorem rcontains_of_contains {I : Interval} {q : ℚ} (h : I.Contains q) : RContains I (q : ℝ) :=
  ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

/-- Conversely, a real enclosure of a rational value IS the rational enclosure (cast reflects order). -/
theorem contains_of_rcontains {I : Interval} {q : ℚ} (h : RContains I (q : ℝ)) : I.Contains q :=
  ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

theorem pt_rcontains (q : ℚ) : RContains (pt q) (q : ℝ) := ⟨le_refl _, le_refl _⟩

theorem add_rcontains {I J : Interval} {x y : ℝ} (hx : RContains I x) (hy : RContains J y) :
    RContains (add I J) (x + y) := by
  refine ⟨?_, ?_⟩
  · show ((I.lo + J.lo : ℚ) : ℝ) ≤ x + y; push_cast; exact add_le_add hx.1 hy.1
  · show x + y ≤ ((I.hi + J.hi : ℚ) : ℝ); push_cast; exact add_le_add hx.2 hy.2

theorem neg_rcontains {I : Interval} {x : ℝ} (hx : RContains I x) : RContains (neg I) (-x) := by
  refine ⟨?_, ?_⟩
  · show ((-I.hi : ℚ) : ℝ) ≤ -x; push_cast; exact neg_le_neg hx.2
  · show -x ≤ ((-I.lo : ℚ) : ℝ); push_cast; exact neg_le_neg hx.1

theorem sub_rcontains {I J : Interval} {x y : ℝ} (hx : RContains I x) (hy : RContains J y) :
    RContains (sub I J) (x - y) := by
  rw [sub_eq_add_neg]; exact add_rcontains hx (neg_rcontains hy)

theorem scale_rcontains (c : ℚ) {I : Interval} {x : ℝ} (hx : RContains I x) :
    RContains (scale c I) ((c : ℝ) * x) := by
  unfold scale
  by_cases hc : 0 ≤ c
  · simp only [hc, if_true]
    refine ⟨?_, ?_⟩
    · show ((c * I.lo : ℚ) : ℝ) ≤ (c : ℝ) * x
      push_cast; exact mul_le_mul_of_nonneg_left hx.1 (by exact_mod_cast hc)
    · show (c : ℝ) * x ≤ ((c * I.hi : ℚ) : ℝ)
      push_cast; exact mul_le_mul_of_nonneg_left hx.2 (by exact_mod_cast hc)
  · simp only [hc, if_false]
    have hcle : (c : ℝ) ≤ 0 := by exact_mod_cast le_of_lt (not_le.mp hc)
    refine ⟨?_, ?_⟩
    · show ((c * I.hi : ℚ) : ℝ) ≤ (c : ℝ) * x
      push_cast; exact mul_le_mul_of_nonpos_left hx.2 hcle
    · show (c : ℝ) * x ≤ ((c * I.lo : ℚ) : ℝ)
      push_cast; exact mul_le_mul_of_nonpos_left hx.1 hcle

/-! ### The four-corner signed product, over `ℝ` (mirrors `CertifiedInterval.mul_contains`). -/

private theorem rmul_le_max_endpoint {a b x y : ℝ} (h1 : a ≤ x) (h2 : x ≤ b) :
    x * y ≤ max (a * y) (b * y) := by
  rcases le_total 0 y with hy | hy
  · exact le_trans (mul_le_mul_of_nonneg_right h2 hy) (le_max_right _ _)
  · exact le_trans (mul_le_mul_of_nonpos_right h1 hy) (le_max_left _ _)

private theorem rmin_endpoint_le_mul {a b x y : ℝ} (h1 : a ≤ x) (h2 : x ≤ b) :
    min (a * y) (b * y) ≤ x * y := by
  rcases le_total 0 y with hy | hy
  · exact le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_right h1 hy)
  · exact le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_right h2 hy)

private theorem rmul_const_le_max {a c d y : ℝ} (h1 : c ≤ y) (h2 : y ≤ d) :
    a * y ≤ max (a * c) (a * d) := by
  rcases le_total 0 a with ha | ha
  · exact le_trans (mul_le_mul_of_nonneg_left h2 ha) (le_max_right _ _)
  · exact le_trans (mul_le_mul_of_nonpos_left h1 ha) (le_max_left _ _)

private theorem rmin_le_mul_const {a c d y : ℝ} (h1 : c ≤ y) (h2 : y ≤ d) :
    min (a * c) (a * d) ≤ a * y := by
  rcases le_total 0 a with ha | ha
  · exact le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_left h1 ha)
  · exact le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_left h2 ha)

theorem mul_rcontains {I J : Interval} {x y : ℝ} (hx : RContains I x) (hy : RContains J y) :
    RContains (mul I J) (x * y) := by
  obtain ⟨ha, hb⟩ := hx
  obtain ⟨hc, hd⟩ := hy
  -- push the four rational corner products to ℝ
  have hlo : ((mul I J).lo : ℝ)
      = min (min ((I.lo:ℝ) * J.lo) ((I.lo:ℝ) * J.hi)) (min ((I.hi:ℝ) * J.lo) ((I.hi:ℝ) * J.hi)) := by
    simp only [mul]; push_cast; ring_nf
  have hhi : ((mul I J).hi : ℝ)
      = max (max ((I.lo:ℝ) * J.lo) ((I.lo:ℝ) * J.hi)) (max ((I.hi:ℝ) * J.lo) ((I.hi:ℝ) * J.hi)) := by
    simp only [mul]; push_cast; ring_nf
  refine ⟨?_, ?_⟩
  · rw [hlo]
    refine le_trans ?_ (rmin_endpoint_le_mul ha hb)
    apply le_min
    · exact le_trans (min_le_left _ _) (rmin_le_mul_const hc hd)
    · exact le_trans (min_le_right _ _) (rmin_le_mul_const hc hd)
  · rw [hhi]
    refine le_trans (rmul_le_max_endpoint ha hb) ?_
    apply max_le
    · exact le_trans (rmul_const_le_max hc hd) (le_max_left _ _)
    · exact le_trans (rmul_const_le_max hc hd) (le_max_right _ _)

theorem pow_rcontains {I : Interval} {x : ℝ} (hx : RContains I x) :
    ∀ n, RContains (I.pow n) (x ^ n)
  | 0 => by simpa [Interval.pow] using pt_rcontains (1 : ℚ)
  | n + 1 => by
    rw [Interval.pow, pow_succ, mul_comm]
    exact mul_rcontains hx (pow_rcontains hx n)

/-- Outward rounding preserves real enclosure (the ℝ analog of `round_contains`). -/
theorem round_rcontains (k : ℕ) {I : Interval} {x : ℝ} (hx : RContains I x) :
    RContains (round k I) x := by
  refine ⟨le_trans ?_ hx.1, le_trans hx.2 ?_⟩
  · exact_mod_cast (round_subset k I).1
  · exact_mod_cast (round_subset k I).2

/-! ## §2 — the additive monoid on `Interval` (so a Fourier sum is an honest `Finset.sum`) -/

instance : AddCommMonoid Interval where
  add := add
  zero := pt 0
  add_assoc a b c := by
    change add (add a b) c = add a (add b c)
    simp only [add, Interval.mk.injEq]; exact ⟨add_assoc _ _ _, add_assoc _ _ _⟩
  zero_add a := by
    change add (pt 0) a = a
    cases a; simp only [add, pt, zero_add]
  add_zero a := by
    change add a (pt 0) = a
    cases a; simp only [add, pt, add_zero]
  add_comm a b := by
    change add a b = add b a
    simp only [add, Interval.mk.injEq]; exact ⟨add_comm _ _, add_comm _ _⟩
  nsmul n I := ⟨n • I.lo, n • I.hi⟩
  nsmul_zero I := by
    change (⟨0 • I.lo, 0 • I.hi⟩ : Interval) = pt 0
    simp only [zero_smul]; rfl
  nsmul_succ n I := by
    change (⟨(n+1) • I.lo, (n+1) • I.hi⟩ : Interval) = add ⟨n • I.lo, n • I.hi⟩ I
    simp only [add, succ_nsmul]

/-- The monoid `+` is `Interval.add` (both endpoints add). -/
theorem interval_add_def (I J : Interval) : I + J = add I J := rfl

/-- The monoid `0` is `pt 0`. -/
theorem interval_zero_lo : (0 : Interval).lo = 0 := rfl
theorem interval_zero_hi : (0 : Interval).hi = 0 := rfl

/-- The monoid zero enclosures `0 : ℝ`. -/
theorem zero_rcontains : RContains (0 : Interval) 0 := by
  rw [RContains, interval_zero_lo, interval_zero_hi]; norm_num

/-- Sum enclosure: if each interval encloses its summand, the interval sum encloses the sum. -/
theorem sum_rcontains {ι : Type*} (s : Finset ι) (G : ι → Interval) (g : ι → ℝ)
    (h : ∀ i ∈ s, RContains (G i) (g i)) :
    RContains (∑ i ∈ s, G i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using zero_rcontains
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, interval_add_def]
      exact add_rcontains (h a (Finset.mem_insert_self _ _))
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-! ## §3 — complex intervals: a box `⟨re, im⟩` of two real-`Interval`s -/

/-- A complex interval: a box `[re.lo, re.hi] × [im.lo, im.hi]` in ℂ. -/
structure CInterval where
  re : Interval
  im : Interval

/-- Complex enclosure: `z`'s real and imaginary parts are each `RContains`ed. -/
def CContains (Z : CInterval) (z : ℂ) : Prop := RContains Z.re z.re ∧ RContains Z.im z.im

/-- Complex interval addition (componentwise). -/
def cadd (Z W : CInterval) : CInterval := ⟨Z.re + W.re, Z.im + W.im⟩

/-- `CInterval` is an additive commutative monoid (the product of two `Interval` monoids). -/
instance : AddCommMonoid CInterval where
  add := cadd
  zero := ⟨0, 0⟩
  add_assoc a b c := by
    change cadd (cadd a b) c = cadd a (cadd b c)
    simp only [cadd, add_assoc]
  zero_add a := by change cadd ⟨0, 0⟩ a = a; cases a; simp only [cadd, zero_add]
  add_zero a := by change cadd a ⟨0, 0⟩ = a; cases a; simp only [cadd, add_zero]
  add_comm a b := by
    change cadd a b = cadd b a
    simp only [cadd, CInterval.mk.injEq]; exact ⟨add_comm _ _, add_comm _ _⟩
  nsmul n Z := ⟨n • Z.re, n • Z.im⟩
  nsmul_zero Z := by
    change (⟨0 • Z.re, 0 • Z.im⟩ : CInterval) = ⟨0, 0⟩
    simp only [zero_smul]
  nsmul_succ n Z := by
    change (⟨(n + 1) • Z.re, (n + 1) • Z.im⟩ : CInterval) = cadd ⟨n • Z.re, n • Z.im⟩ Z
    simp only [cadd, succ_nsmul]

theorem cinterval_add_def (Z W : CInterval) : Z + W = cadd Z W := rfl
theorem cinterval_zero_re : (0 : CInterval).re = 0 := rfl
theorem cinterval_zero_im : (0 : CInterval).im = 0 := rfl

/-- Complex interval negation, subtraction, the four-real-multiply product, and conjugation. -/
def cneg (Z : CInterval) : CInterval := ⟨neg Z.re, neg Z.im⟩
def csub (Z W : CInterval) : CInterval := ⟨sub Z.re W.re, sub Z.im W.im⟩
def cmul (Z W : CInterval) : CInterval :=
  ⟨sub (mul Z.re W.re) (mul Z.im W.im), add (mul Z.re W.im) (mul Z.im W.re)⟩
/-- Complex-interval conjugation: negate the imaginary box. -/
def cconjI (Z : CInterval) : CInterval := ⟨Z.re, neg Z.im⟩

/-- The point complex interval at a rational-coordinate complex number. -/
def cpt (a b : ℚ) : CInterval := ⟨pt a, pt b⟩

/-! ### §3.1 — complex arithmetic enclosure (all inherited from real-interval enclosure) -/

theorem czero_ccontains : CContains (0 : CInterval) 0 := by
  refine ⟨?_, ?_⟩
  · rw [cinterval_zero_re]; simpa using zero_rcontains
  · rw [cinterval_zero_im]; simpa using zero_rcontains

theorem cadd_ccontains {Z W : CInterval} {z w : ℂ} (hz : CContains Z z) (hw : CContains W w) :
    CContains (cadd Z W) (z + w) := by
  refine ⟨?_, ?_⟩
  · rw [Complex.add_re, cadd]; exact add_rcontains hz.1 hw.1
  · rw [Complex.add_im, cadd]; exact add_rcontains hz.2 hw.2

theorem cneg_ccontains {Z : CInterval} {z : ℂ} (hz : CContains Z z) : CContains (cneg Z) (-z) := by
  refine ⟨?_, ?_⟩
  · rw [Complex.neg_re, cneg]; exact neg_rcontains hz.1
  · rw [Complex.neg_im, cneg]; exact neg_rcontains hz.2

theorem cmul_ccontains {Z W : CInterval} {z w : ℂ} (hz : CContains Z z) (hw : CContains W w) :
    CContains (cmul Z W) (z * w) := by
  refine ⟨?_, ?_⟩
  · rw [Complex.mul_re, cmul]; exact sub_rcontains (mul_rcontains hz.1 hw.1) (mul_rcontains hz.2 hw.2)
  · rw [Complex.mul_im, cmul]; exact add_rcontains (mul_rcontains hz.1 hw.2) (mul_rcontains hz.2 hw.1)

theorem cconj_ccontains {Z : CInterval} {z : ℂ} (hz : CContains Z z) :
    CContains (cconjI Z) ((starRingEnd ℂ) z) := by
  refine ⟨?_, ?_⟩
  · rw [Complex.conj_re, cconjI]; exact hz.1
  · rw [Complex.conj_im, cconjI]; exact neg_rcontains hz.2

theorem cpt_ccontains (a b : ℚ) : CContains (cpt a b) (⟨a, b⟩ : ℂ) :=
  ⟨pt_rcontains a, pt_rcontains b⟩

/-- Complex interval power by repeated `cmul`. -/
def cpow (Z : CInterval) : ℕ → CInterval
  | 0 => cpt 1 0
  | n + 1 => cmul Z (cpow Z n)

theorem cone_ccontains : CContains (cpt 1 0) (1 : ℂ) := by
  have h1 : (1 : ℂ) = ⟨1, 0⟩ := Complex.ext (by simp) (by simp)
  rw [h1]
  exact_mod_cast cpt_ccontains 1 0

theorem cpow_ccontains {Z : CInterval} {z : ℂ} (hz : CContains Z z) :
    ∀ n, CContains (cpow Z n) (z ^ n)
  | 0 => by simpa [cpow] using cone_ccontains
  | n + 1 => by
    rw [cpow, pow_succ, mul_comm]
    exact cmul_ccontains hz (cpow_ccontains hz n)

/-- Complex sum enclosure — the Fourier-sum workhorse. -/
theorem csum_ccontains {ι : Type*} (s : Finset ι) (G : ι → CInterval) (g : ι → ℂ)
    (h : ∀ i ∈ s, CContains (G i) (g i)) :
    CContains (∑ i ∈ s, G i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using czero_ccontains
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, cinterval_add_def]
      exact cadd_ccontains (h a (Finset.mem_insert_self _ _))
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- Scale a complex interval by an exact rational (multiply the box by `c : ℚ`). -/
def cscaleQ (c : ℚ) (Z : CInterval) : CInterval := ⟨scale c Z.re, scale c Z.im⟩

theorem cscaleQ_ccontains (c : ℚ) {Z : CInterval} {z : ℂ} (hz : CContains Z z) :
    CContains (cscaleQ c Z) ((c : ℂ) * z) := by
  have hre : ((c : ℂ) * z).re = (c : ℝ) * z.re := by
    simp [Complex.mul_re]
  have him : ((c : ℂ) * z).im = (c : ℝ) * z.im := by
    simp [Complex.mul_im]
  exact ⟨by rw [hre, cscaleQ]; exact scale_rcontains c hz.1,
         by rw [him, cscaleQ]; exact scale_rcontains c hz.2⟩

/-! ## §4 — the exact complex DFT / IDFT / circular convolution (what the intervals must enclose)

`ζ_N = exp(2πi/N)` is Mathlib's canonical primitive `N`-th root of unity
(`Complex.isPrimitiveRoot_exp`). The forward DFT is the Vandermonde evaluation `∑_j a_j ζ^{jk}`; the inverse
uses the conjugate kernel `conj(ζ^{nk}) = ζ^{-nk}` and the `1/N` scale. -/

/-- The canonical primitive `N`-th root of unity `exp(2πi/N)`. -/
noncomputable def zeta (N : ℕ) : ℂ := Complex.exp (2 * ↑Real.pi * Complex.I / ↑N)

/-- Forward DFT: `(dft a) k = ∑_j a_j ζ^{jk}`. -/
noncomputable def dft {N : ℕ} (a : Fin N → ℂ) : Fin N → ℂ :=
  fun k => ∑ j : Fin N, a j * (zeta N) ^ (j.val * k.val)

/-- Inverse DFT (conjugate kernel, `1/N` scale): `(idft A) n = (1/N) ∑_k A_k · conj(ζ^{nk})`. -/
noncomputable def idft {N : ℕ} (A : Fin N → ℂ) : Fin N → ℂ :=
  fun n => (∑ k : Fin N, A k * (starRingEnd ℂ) ((zeta N) ^ (n.val * k.val))) / (N : ℂ)

/-- Circular (cyclic) convolution on `Fin N` (subtraction is mod `N`): `(cconv a b) n = ∑_j a_j b_{n-j}`. -/
noncomputable def cconv {N : ℕ} (a b : Fin N → ℂ) : Fin N → ℂ :=
  fun n => ∑ j : Fin N, a j * b (n - j)

/-- `ζ_N = exp(↑(2π/N)·I)`. -/
theorem zeta_eq_exp (N : ℕ) : zeta N = Complex.exp (((2 * Real.pi / N : ℝ)) * Complex.I) := by
  rw [zeta]; congr 1; push_cast; ring

/-! ## §5 — the interval DFT / IDFT over a certified root table, and the enclosure theorems

A **certified root table** is any `W : ℕ → CInterval` with `∀ m, CContains (W m) (ζ_N^m)`. The interval
transforms replace each exact `ζ^{jk}` by `W (j*k)` and each `conj(ζ^{nk})` by `cconjI (W (n*k))`, so by the
complex-interval arithmetic enclosure they BRACKET the exact complex transforms coefficient by coefficient. -/

/-- Interval forward DFT over a certified root table `W`. -/
def dftI {N : ℕ} (F : Fin N → CInterval) (W : ℕ → CInterval) : Fin N → CInterval :=
  fun k => ∑ j : Fin N, cmul (F j) (W (j.val * k.val))

/-- Interval inverse DFT over a certified root table `W` (conjugate kernel, `1/N` scale). -/
def idftI {N : ℕ} (A : Fin N → CInterval) (W : ℕ → CInterval) : Fin N → CInterval :=
  fun n => cscaleQ (1 / (N : ℚ)) (∑ k : Fin N, cmul (A k) (cconjI (W (n.val * k.val))))

/-- **THE FORWARD-DFT ENCLOSURE.** The interval DFT brackets the exact complex DFT. -/
theorem dftI_contains {N : ℕ} {F : Fin N → CInterval} {a : Fin N → ℂ}
    (W : ℕ → CInterval) (hW : ∀ m, CContains (W m) ((zeta N) ^ m))
    (hF : ∀ j, CContains (F j) (a j)) (k : Fin N) :
    CContains (dftI F W k) (dft a k) := by
  refine csum_ccontains _ _ _ (fun j _ => ?_)
  exact cmul_ccontains (hF j) (hW (j.val * k.val))

/-- **THE INVERSE-DFT ENCLOSURE.** The interval IDFT brackets the exact complex IDFT. -/
theorem idftI_contains {N : ℕ} {A : Fin N → CInterval} {Ac : Fin N → ℂ}
    (W : ℕ → CInterval) (hW : ∀ m, CContains (W m) ((zeta N) ^ m))
    (hA : ∀ k, CContains (A k) (Ac k)) (n : Fin N) :
    CContains (idftI A W n) (idft Ac n) := by
  have hinner : CContains (∑ k : Fin N, cmul (A k) (cconjI (W (n.val * k.val))))
      (∑ k : Fin N, Ac k * (starRingEnd ℂ) ((zeta N) ^ (n.val * k.val))) := by
    refine csum_ccontains _ _ _ (fun k _ => ?_)
    exact cmul_ccontains (hA k) (cconj_ccontains (hW (n.val * k.val)))
  have hscale := cscaleQ_ccontains (1 / (N : ℚ)) hinner
  rw [idft, idftI]
  have hcast : ((1 / (N : ℚ) : ℚ) : ℂ) = 1 / (N : ℂ) := by push_cast; ring
  have heq : (∑ k : Fin N, Ac k * (starRingEnd ℂ) ((zeta N) ^ (n.val * k.val))) / (N : ℂ)
      = ((1 / (N : ℚ) : ℚ) : ℂ) * (∑ k : Fin N, Ac k * (starRingEnd ℂ) ((zeta N) ^ (n.val * k.val))) := by
    rw [hcast, div_eq_mul_inv, one_div, mul_comm]
  rw [heq]
  exact hscale

/-! ## §5b — the exact complex DFT convolution theorem `IDFT(DFT a ⊙ DFT b) = a ⊛ b`

The classical identity, proved kernel-clean from roots-of-unity orthogonality (`Complex.isPrimitiveRoot_exp`,
`geom_sum_eq`). This is what turns the interval-IDFT-of-product-of-interval-DFTs enclosure into an enclosure of
the exact convolution. -/

theorem zeta_ne_zero (N : ℕ) : zeta N ≠ 0 := Complex.exp_ne_zero _

theorem norm_zeta (N : ℕ) : ‖zeta N‖ = 1 := by
  rw [zeta_eq_exp, Complex.norm_exp_ofReal_mul_I]

theorem conj_zeta (N : ℕ) : (starRingEnd ℂ) (zeta N) = (zeta N)⁻¹ :=
  (Complex.inv_eq_conj (norm_zeta N)).symm

theorem conj_zeta_pow (N : ℕ) (p : ℕ) : (starRingEnd ℂ) ((zeta N) ^ p) = ((zeta N) ^ p)⁻¹ := by
  rw [map_pow, conj_zeta, inv_pow]

/-- Geometric sum of an `N`-th root of unity `w`: `N` if `w = 1`, else `0`. -/
theorem geom_root_sum {N : ℕ} (w : ℂ) (hw : w ^ N = 1) :
    ∑ k : Fin N, w ^ k.val = if w = 1 then (N : ℂ) else 0 := by
  by_cases h1 : w = 1
  · rw [if_pos h1, h1]; simp
  · rw [if_neg h1, Fin.sum_univ_eq_sum_range (fun i => w ^ i) N, geom_sum_eq h1 N, hw]
    simp

/-- **THE COMPLEX DFT CONVOLUTION THEOREM (kernel-clean).** `IDFT(DFT a ⊙ DFT b) = a ⊛ b` (circular). -/
theorem idft_dft_mul {N : ℕ} (hN : 0 < N) (a b : Fin N → ℂ) :
    idft (fun k => dft a k * dft b k) = cconv a b := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  have hpr : IsPrimitiveRoot (zeta (m + 1)) (m + 1) :=
    Complex.isPrimitiveRoot_exp (m + 1) (Nat.succ_ne_zero m)
  have hgN : (zeta (m + 1)) ^ (m + 1) = 1 := hpr.pow_eq_one
  have geomZ : ∀ (e : ℤ), (∑ k : Fin (m + 1), ((zeta (m + 1)) ^ e) ^ k.val)
      = if ((m + 1 : ℕ) : ℤ) ∣ e then ((m + 1 : ℕ) : ℂ) else 0 := by
    intro e
    have hbase : ((zeta (m + 1)) ^ e) ^ (m + 1) = 1 := by
      rw [← zpow_natCast ((zeta (m + 1)) ^ e) (m + 1), ← zpow_mul, mul_comm, zpow_mul,
          zpow_natCast, hgN, one_zpow]
    rw [geom_root_sum _ hbase]
    exact if_congr (hpr.zpow_eq_one_iff_dvd e) rfl rfl
  funext n
  simp only [idft, cconv]
  have hWz : ∀ i j : Fin (m + 1),
      (zeta (m + 1)) ^ (i.val) * (zeta (m + 1)) ^ (j.val) * ((zeta (m + 1)) ^ (n.val))⁻¹
        = (zeta (m + 1)) ^ ((i.val : ℤ) + (j.val : ℤ) - (n.val : ℤ)) := by
    intro i j
    rw [← zpow_natCast (zeta (m + 1)) i.val, ← zpow_natCast (zeta (m + 1)) j.val,
        ← zpow_natCast (zeta (m + 1)) n.val, ← zpow_neg,
        ← zpow_add₀ (zeta_ne_zero _), ← zpow_add₀ (zeta_ne_zero _)]
    ring_nf
  have keyiff : ∀ i j : Fin (m + 1),
      ((m + 1 : ℕ) : ℤ) ∣ ((i.val : ℤ) + (j.val : ℤ) - (n.val : ℤ)) ↔ j = n - i := by
    intro i j
    rw [eq_sub_iff_add_eq, Fin.ext_iff, Fin.val_add]
    rw [show ((i.val : ℤ) + (j.val : ℤ) - (n.val : ℤ))
          = ((i.val + j.val : ℕ) : ℤ) - ((n.val : ℕ) : ℤ) by push_cast; ring]
    rw [← Nat.modEq_iff_dvd, Nat.ModEq, Nat.mod_eq_of_lt n.isLt, add_comm j.val i.val]
    exact eq_comm
  have step1 : ∀ k : Fin (m + 1),
      (dft a k * dft b k) * (starRingEnd ℂ) ((zeta (m + 1)) ^ (n.val * k.val))
        = ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
            a i * b j *
              ((zeta (m + 1)) ^ (i.val) * (zeta (m + 1)) ^ (j.val)
                * ((zeta (m + 1)) ^ (n.val))⁻¹) ^ k.val := by
    intro k
    simp only [dft]
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [conj_zeta_pow]
    simp only [pow_mul, mul_pow, inv_pow]
    ring
  have hnum :
      (∑ k : Fin (m + 1),
          (dft a k * dft b k) * (starRingEnd ℂ) ((zeta (m + 1)) ^ (n.val * k.val)))
        = ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
            a i * b j *
              (if ((m + 1 : ℕ) : ℤ) ∣ ((i.val : ℤ) + (j.val : ℤ) - (n.val : ℤ))
                then ((m + 1 : ℕ) : ℂ) else 0) := by
    rw [Finset.sum_congr rfl (fun k _ => step1 k), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.mul_sum, hWz i j, geomZ]
  rw [hnum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_div]
  have hterm : ∀ j : Fin (m + 1),
      (a i * b j *
          (if ((m + 1 : ℕ) : ℤ) ∣ ((i.val : ℤ) + (j.val : ℤ) - (n.val : ℤ))
            then ((m + 1 : ℕ) : ℂ) else 0)) / ((m + 1 : ℕ) : ℂ)
        = if j = n - i then a i * b j else 0 := by
    intro j
    by_cases hj : j = n - i
    · rw [if_pos ((keyiff i j).mpr hj), if_pos hj, mul_div_assoc,
        div_self (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)), mul_one]
    · rw [if_neg (fun h => hj ((keyiff i j).mp h)), if_neg hj, mul_zero, zero_div]
  rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]

/-! ## §5c — THE FFT-CONVOLUTION CONTAINMENT (the centerpiece)

Composing `idftI_contains` (interval IDFT brackets exact IDFT) and `dftI_contains` (interval DFT brackets exact
DFT) with the exact identity `idft_dft_mul`: the interval FFT-convolution `IDFT(DFT F ⊙ DFT G)` brackets the
EXACT circular convolution `cconv a b` of the enclosed coefficient vectors. -/

/-- Interval FFT-convolution over a certified root table `W`. -/
def fftConvI {N : ℕ} (F G : Fin N → CInterval) (W : ℕ → CInterval) : Fin N → CInterval :=
  fun n => idftI (fun k => cmul (dftI F W k) (dftI G W k)) W n

/-- **THE FFT-CONVOLUTION CONTAINMENT.** For any certified root table `W ⊇ ζ_N^·` and interval coefficient
vectors `F ⊇ a`, `G ⊇ b`, the interval FFT-convolution brackets the EXACT circular convolution `a ⊛ b`. -/
theorem fftConvI_contains {N : ℕ} (hN : 0 < N) {F G : Fin N → CInterval} {a b : Fin N → ℂ}
    (W : ℕ → CInterval) (hW : ∀ m, CContains (W m) ((zeta N) ^ m))
    (hF : ∀ j, CContains (F j) (a j)) (hG : ∀ j, CContains (G j) (b j)) (n : Fin N) :
    CContains (fftConvI F G W n) (cconv a b n) := by
  have hprod : ∀ k : Fin N,
      CContains (cmul (dftI F W k) (dftI G W k)) (dft a k * dft b k) :=
    fun k => cmul_ccontains (dftI_contains W hW hF k) (dftI_contains W hW hG k)
  have h := idftI_contains (A := fun k => cmul (dftI F W k) (dftI G W k))
    (Ac := fun k => dft a k * dft b k) W hW hprod n
  rw [fftConvI]
  rw [← idft_dft_mul hN a b]
  exact h

/-! ## §6 — certified roots of unity

`ζ_N` written as `exp(↑(2π/N)·I)` gives `(ζ_N).re = cos(2π/N)`, `(ζ_N).im = sin(2π/N)`. A certified
complex-interval seed `Wz ⊇ ζ_N` plus the `cpow` recurrence (`cpow_ccontains`) yields a full certified root
table `m ↦ cpow Wz m ⊇ ζ_N^m` — the "algebraic recurrence `ω^{k+1} = ω·ω^k` carried in intervals". §6.1 gives
the exact rational seed for `N = 4` (`ζ_4 = i`); §6.2 the general Taylor-remainder cos/sin enclosures (from
`Real.cos_bound`/`Real.sin_bound` + rational angle bounds) that produce a certified seed for any `N` with
`2π/N ≤ 1`. -/

theorem zeta_re (N : ℕ) : (zeta N).re = Real.cos (2 * Real.pi / N) := by
  rw [zeta_eq_exp, Complex.exp_ofReal_mul_I_re]

theorem zeta_im (N : ℕ) : (zeta N).im = Real.sin (2 * Real.pi / N) := by
  rw [zeta_eq_exp, Complex.exp_ofReal_mul_I_im]

/-- **Any certified seed gives a certified root table via the interval power recurrence.** -/
theorem cpow_seed_root_table {N : ℕ} {Wz : CInterval} (hz : CContains Wz (zeta N)) :
    ∀ m, CContains (cpow Wz m) ((zeta N) ^ m) :=
  fun m => cpow_ccontains hz m

/-! ### §6.1 — the exact rational seed for `N = 4` (`ζ_4 = i`). -/

theorem zeta4_eq_I : zeta 4 = Complex.I := by
  have hθ : (2 * Real.pi / (4 : ℕ) : ℝ) = Real.pi / 2 := by push_cast; ring
  apply Complex.ext
  · rw [zeta_re, hθ, Real.cos_pi_div_two, Complex.I_re]
  · rw [zeta_im, hθ, Real.sin_pi_div_two, Complex.I_im]

/-- The exact certified seed for `N = 4`: the point complex interval at `i`. -/
def zetaSeed4 : CInterval := cpt 0 1

theorem zetaSeed4_contains : CContains zetaSeed4 (zeta 4) := by
  rw [zetaSeed4, zeta4_eq_I]
  refine ⟨?_, ?_⟩
  · rw [Complex.I_re]; simpa [cpt] using pt_rcontains (0 : ℚ)
  · rw [Complex.I_im]; simpa [cpt] using pt_rcontains (1 : ℚ)

/-- The full certified root table for `N = 4` (exact, no analytic residual). -/
theorem zetaSeed4_root_table : ∀ m, CContains (cpow zetaSeed4 m) ((zeta 4) ^ m) :=
  cpow_seed_root_table zetaSeed4_contains

/-! ### §6.2 — general certified cos/sin enclosures (Taylor degree ≤ 3 + `Real.cos_bound`/`sin_bound`).

For an angle `θ` with a rational bracket `a ≤ θ ≤ b`, `0 ≤ a`, `b ≤ 1`, the degree-2/3 Taylor polynomials with
Mathlib's uniform remainder `|θ|⁴·5/96` give rational-endpoint enclosures of `cos θ` and `sin θ`. These are the
certified seed ingredients for any `N` with `2π/N ≤ 1` (i.e. `N ≥ 7`): take `a,b` from `Real.pi_gt_d6`/`pi_lt_d6`. -/

/-- Certified `cos` enclosure from a rational angle bracket. -/
theorem cos_rcontains_of {θ : ℝ} {a b : ℚ} (ha : 0 ≤ a) (hb : b ≤ 1)
    (hlo : (a : ℝ) ≤ θ) (hhi : θ ≤ (b : ℝ)) :
    RContains ⟨1 - b ^ 2 / 2 - b ^ 4 * (5 / 96), 1 - a ^ 2 / 2 + b ^ 4 * (5 / 96)⟩ (Real.cos θ) := by
  have haR : (0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hbR : (b : ℝ) ≤ 1 := by exact_mod_cast hb
  have hθ0 : 0 ≤ θ := le_trans haR hlo
  have hθ1 : |θ| ≤ 1 := by rw [abs_of_nonneg hθ0]; exact le_trans hhi hbR
  have hbnd := Real.cos_bound hθ1
  rw [abs_le] at hbnd
  have habs : |θ| = θ := abs_of_nonneg hθ0
  rw [habs] at hbnd
  have hθ2 : θ ^ 2 ≤ (b : ℝ) ^ 2 := pow_le_pow_left₀ hθ0 hhi 2
  have hθ4 : θ ^ 4 ≤ (b : ℝ) ^ 4 := pow_le_pow_left₀ hθ0 hhi 4
  have ha2 : (a : ℝ) ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ haR hlo 2
  refine ⟨?_, ?_⟩
  · show ((1 - b ^ 2 / 2 - b ^ 4 * (5 / 96) : ℚ) : ℝ) ≤ Real.cos θ
    push_cast; nlinarith [hbnd.1, hθ2, hθ4]
  · show Real.cos θ ≤ ((1 - a ^ 2 / 2 + b ^ 4 * (5 / 96) : ℚ) : ℝ)
    push_cast; nlinarith [hbnd.2, ha2, hθ4]

/-- Certified `sin` enclosure from a rational angle bracket. -/
theorem sin_rcontains_of {θ : ℝ} {a b : ℚ} (ha : 0 ≤ a) (hb : b ≤ 1)
    (hlo : (a : ℝ) ≤ θ) (hhi : θ ≤ (b : ℝ)) :
    RContains ⟨a - b ^ 3 / 6 - b ^ 4 * (5 / 96), b - a ^ 3 / 6 + b ^ 4 * (5 / 96)⟩ (Real.sin θ) := by
  have haR : (0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hbR : (b : ℝ) ≤ 1 := by exact_mod_cast hb
  have hθ0 : 0 ≤ θ := le_trans haR hlo
  have hθ1 : |θ| ≤ 1 := by rw [abs_of_nonneg hθ0]; exact le_trans hhi hbR
  have hbnd := Real.sin_bound hθ1
  rw [abs_le] at hbnd
  have habs : |θ| = θ := abs_of_nonneg hθ0
  rw [habs] at hbnd
  have hθ3 : θ ^ 3 ≤ (b : ℝ) ^ 3 := pow_le_pow_left₀ hθ0 hhi 3
  have ha3 : (a : ℝ) ^ 3 ≤ θ ^ 3 := pow_le_pow_left₀ haR hlo 3
  have hθ4 : θ ^ 4 ≤ (b : ℝ) ^ 4 := pow_le_pow_left₀ hθ0 hhi 4
  -- Mathlib's `Real.sin_bound` remainder is `|θ|⁵/100`; on `[0,1]` it is below `θ⁴·5/96`.
  have hθ54 : θ ^ 5 ≤ θ ^ 4 := pow_le_pow_of_le_one hθ0 (le_trans hhi hbR) (by norm_num)
  refine ⟨?_, ?_⟩
  · show ((a - b ^ 3 / 6 - b ^ 4 * (5 / 96) : ℚ) : ℝ) ≤ Real.sin θ
    push_cast; nlinarith [hbnd.1, hθ3, hθ4, hθ54, hlo]
  · show Real.sin θ ≤ ((b - a ^ 3 / 6 + b ^ 4 * (5 / 96) : ℚ) : ℝ)
    push_cast; nlinarith [hbnd.2, ha3, hθ4, hθ54, hhi]

/-! ## §6.3 — the bridge back to `CertifiedInterval.Interval` ℚ-`Contains`

The ML-KEM convolution coefficients are exact rationals (integer counts). When the exact convolution value at an
index is a real rational, the FFT output's real-part box `Contains` it in the ℚ sense — reconnecting to the
`IntervalConvolution` tail machinery (`ivTailSum`, `exactTailFrac_of_interval`, `exactConvTailFrac_closes_delta`),
which sums `hi`-endpoints of `Interval`s over the escaping indices. -/

/-- **THE RATIONAL BRIDGE.** When the exact circular convolution value `cconv a b n` is a real rational `q`, the
interval FFT-convolution's real-part box ℚ-`Contains` `q`. -/
theorem fftConv_re_contains_rat {N : ℕ} (hN : 0 < N) {F G : Fin N → CInterval} {a b : Fin N → ℂ}
    (W : ℕ → CInterval) (hW : ∀ m, CContains (W m) ((zeta N) ^ m))
    (hF : ∀ j, CContains (F j) (a j)) (hG : ∀ j, CContains (G j) (b j))
    (n : Fin N) (q : ℚ) (hq : cconv a b n = (q : ℂ)) :
    (fftConvI F G W n).re.Contains q := by
  have h := (fftConvI_contains hN W hW hF hG n).1
  rw [hq] at h
  have hre : ((q : ℂ)).re = ((q : ℚ) : ℝ) := by simp
  rw [hre] at h
  exact contains_of_rcontains h

/-! ## §7 — ASSESSMENT: the ML-KEM-768 δ instance and the precisely-named remaining kernel-eval cost.

**What is CLOSED here (kernel-clean, reusable, upstreamable).** A certified frequency-domain convolution:
signed complex interval arithmetic (`CInterval`, `cmul`/`cpow`/`cconjI`/`cscaleQ`, all enclosure-proved on the
`CertifiedInterval` bedrock), the interval DFT/IDFT over a certified root table (`dftI`/`idftI`) with the
enclosure theorems `dftI_contains`/`idftI_contains`, the exact complex DFT convolution theorem `idft_dft_mul`
(orthogonality, kernel-clean), and their composition `fftConvI_contains` — **the interval frequency-domain
convolution provably BRACKETS the exact circular convolution `a ⊛ b`**. Certified roots of unity: the exact
`N = 4` seed (`ζ_4 = i`) with the `cpow` recurrence, and the general Taylor cos/sin enclosures
(`cos_rcontains_of`/`sin_rcontains_of`) for any `N` with `2π/N ≤ 1`. The rational bridge
`fftConv_re_contains_rat` reconnects the output to `IntervalConvolution`'s ℚ tail machinery.

**The δ object (`MlKemDelta` §16/§19).** The per-coefficient light-law is `prodCounts^{⊛2304} ⊛ cbdCounts ⊛
cErrLaw` (`LightExactPerCoeffTail` = residual **R1**), support `≈[−9300, 9300]` (`≈18600` wide); FIPS needs the
per-coefficient tail `≤ 2⁻¹⁷⁴` (true value `≈2⁻¹⁸⁰`, `~6`-bit margin), which `exactConvTailFrac_closes_delta`
turns into `δ ≤ 2⁻¹⁶⁴`. R2 is already discharged (§18–19 supply the true `cErrLaw`); the sole wall is R1's tail
evaluation. To drive R1 by THIS route: zero-pad the count lists to `N = 2¹⁵ = 32768` (`> 2·18600`, so circular
convolution equals linear), take `DFT(prodCounts)`, raise it POINTWISE to the `2304`-th power (`O(N·log 2304)`,
the frequency-domain win for a high self-convolution power — transform once, power pointwise, invert once, vs
`~14` schoolbook `O(N²)` convolutions), pointwise-multiply by `DFT(cbdCounts)` and `DFT(cErrLaw)`, `IDFT`, read
the real-part boxes, and feed their escaping-index `hi`-sum through `fftConv_re_contains_rat` +
`exactTailFrac_of_interval` into `exactConvTailFrac_closes_delta`.

**The precisely-named remaining cost (why R1 is still a wall even with this layer).**
1. **The `2304`-fold frequency-domain power containment** (`idft((dftI F)^{2304}) ⊇ prodCounts^{⊛2304}`). The
   proven `fftConvI_contains` closes the `2`-fold case; the `p`-fold power needs two further standard lemmas from
   the SAME orthogonality toolkit as `idft_dft_mul`: the forward convolution theorem `dft (cconv a b) = dft a ⊙
   dft b` and the inversion `idft (dft a) = a`, from which `cconv^{(p)} a = idft ((dft a)^p)` by induction. Plus
   the elementary linear-equals-circular zero-padding lemma (support `< N`). Scoped, not open-ended.
2. **Kernel EVALUATION at `N = 32768`.** `dftI`/`idftI` here are the DIRECT `O(N²)` Vandermonde DFT (the general
   form the containment is proved for), i.e. `≈N² ≈ 10⁹` complex-interval multiplies per transform — beyond
   kernel `decide` (`~10⁶`–`10⁷`-op practical reach). The `O(N log N)` **radix-2 recursive** interval-FFT (which
   REUSES this file's `cmul`/`cadd`/certified roots unchanged, with its own butterfly-recursion containment
   proof) brings a transform to `≈3·10⁵` ops; the whole R1 evaluation then `≈10⁶` complex-interval ops at
   `~200`-bit precision — the EDGE of kernel feasibility (raised heartbeats). Building that fast FFT + running it
   in-kernel is the residual. To dodge the `Rat` gcd-normalization stall the foundation flagged, round each
   endpoint to `k`-bit dyadics after every op via `CertifiedInterval.round` (supported here by `round_rcontains`)
   — fixed-denominator arithmetic, no gcd blowup.

**Bottom line.** The certified frequency-domain convolution + its containment theorem: BUILT + PROVEN + kernel-
clean. Certified roots of unity: BUILT (exact `N=4`; general Taylor seed). δ closure by this route: reduced to
(1) the `p`-fold power lift (standard, same toolkit) and (2) the `O(N log N)` radix-2 interval-FFT + its
`N=32768` kernel run — the precisely-scoped remaining cost. The containment layer is reusable regardless. -/

end Dregg2.ForMathlib.IntervalFFT

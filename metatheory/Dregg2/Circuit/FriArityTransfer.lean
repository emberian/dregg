import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Dregg2.Circuit.BabyBearFriField

/-!
# `FriArityTransfer` — the ARITY-GENERIC good-challenge count, and the DEPLOYED arity-8 per-fold bound

**Why this file exists.** `FriCorrelatedAgreementSharp.lean` §8 proves the standing **~112.6-bit**
per-fold posture (`wrap_perFold_soundness_capacity`) over a **2-to-1** fold
(`Fold geom α f = E f + α · O f`, `Fin (2^7) → Fin (2^6)`). The **DEPLOYED** config folds at
**ARITY 8** (`IR2_FRI_MAX_LOG_ARITY = 3`, `circuit/src/descriptor_ir2.rs:5448`; also
`plonky3_prover.rs:120` and `PROD_FRI_MAX_LOG_ARITY`). The transfer of the ~112.6 figure from the
2-to-1 model to arity-8 folding was **NOT mechanized** — the standing posture rested on an unproven
transfer (the residual named in `circuit/tests/fri_params_soundness_budget.rs`'s header).

This file closes the MATHEMATICAL core of that transfer, and reports the honest number.

## The deployed fold really is a degree-`(m−1)` moment curve

The pinned plonky3 rev (`82cfad73cd734d37a0d51953094f970c531817ec`, `fri/src/two_adic_pcs.rs`,
`fold_row`) computes `lagrange_interpolate_at(xs, evals, beta)` — the degree-`< 8` interpolation of
the `8` coset evaluations, evaluated at `β`. In the phase decomposition
`f(x) = Σ_{i<m} x^i · g_i(x^m)` the arity-`m` fold is

  `Fold_β f (y) = Σ_{i<m} β^i · g_i(y)`

— a degree-`(m−1)` MOMENT CURVE in `β`, not the affine LINE `E f + α · O f` of the `m = 2` model.
(`fold_matrix` decomposes an arity-`2^k` fold into `k` sequential arity-`2` folds with the
ALGEBRAICALLY DEPENDENT challenges `β, β², β⁴, …` — see §4 for why that route does NOT give a sound
transfer, and this direct route does.)

## Relation to `FriFoldArity.lean` — what was ALREADY arity-8, and what was NOT

`Dregg2.Circuit.FriFoldArity` already generalizes the FOLD-CLOSE RECONSTRUCTION to arity `n`
(`fold_close_of_arity_challenges`: `n` DISTINCT challenges each folding `d`-close ⟹ `f` is
`n²·d`-close), and its arity-`n` fold model `Σ_{j<n} αᵢ^j · Cⱼf(y)` is EXACTLY the moment curve `H`
below — the two models agree. That file is the unique-decoding, BBHR18-Vandermonde side.

What it does NOT give is the PROXIMITY-GAP COUNT that the ~112.6 posture is made of. Its cardinality
tooth `good_challenge_card_lt` (`|Good| < n`) requires `Fold α f ∈ S.C'` — the fold landing EXACTLY
in the folded code (`d = 0`), the degenerate radius. The deployed posture lives at `dIn = 62` (the
fold is `62`-CLOSE, not exact), and at that radius the tree's only count is §8's arity-2
`C(64,2) = 2016`. This file supplies the missing arity-8 count at the REAL radius.

## §1's theorem — and why it is the RIGHT generalization

`good_card_le_of_phase_injective` counts, for a family of "good" challenges `β` whose fold is a
CONSTANT on a large agreement set `S β`, by a PAIR double-count:

  for `y ≠ z`, `H y (T) − H z (T) = Σ_{i<m} (Φ i y − Φ i z) · T^i` is a NONZERO polynomial of degree
  `≤ m−1` (nonzero exactly because the fiber map `Φ` is INJECTIVE — the `M = 1` far-fiber bound), and
  every good `β` with `{y,z} ⊆ S β` is a ROOT of it (both points fold to the SAME constant `c β`).
  So each PAIR `{y,z}` lies in at most `m−1` of the sets `S β`, giving

    `Σ_{β ∈ Good} C(|S β|, 2) ≤ (m−1) · C(|κ|, 2)`,  hence  `|Good| · C(s,2) ≤ (m−1) · C(|κ|,2)`.

**It specializes to §8 EXACTLY.** At `m = 2`, `|κ| = 64`, `s = 2` it gives `|Good| ≤ 1 · C(64,2) =
2016` — the very count `wrap_good_challenge_card_le_capacity` proves by its pair-injection. This is
the sanity check that the generalization is the right one (`arity2_recovers_capacity_count`, §3).

At `m = 8`, `|κ| = 64`, `s = 2` it gives `|Good| ≤ 7 · C(64,2) = 14112` — the arity-8 count.

## ⚑ THE HONEST NUMBER — the deployed arity-8 posture is **~109.84 bits, BELOW ~112.6**

`|Good| ≤ 14112` over the deployed quartic challenge field `|F| = babyBearP⁴ ≈ 2^123.6` gives the
per-fold error `14112 / babyBearP⁴ < 2⁻¹⁰⁹` (`arity8_perFold_soundness`), i.e. **~109.84 proven
bits** — exactly `log₂ 7 ≈ 2.807` bits BELOW the arity-2 `~112.65`
(`arity8_loses_exactly_factor_seven`, `arity8_bound_is_seven_times_arity2`). The loss is not slack in
the argument: it is the degree-`7` moment curve: a PAIR of points can lie in as many as `7` good
agreement sets, where the affine line admits only `1`.

**This is a REAL FINDING about the deployed posture, reported unmassaged**: the standing ~112.6
(`docs/reference/FRI-PARAM-FRONTIER.md`, `wrap_perFold_soundness_capacity`) is proved for a fold the
deployed prover does NOT run. At the deployed arity 8 the same method proves **~109.84**. The ~112.6
figure is recovered at arity 8 only by STRENGTHENING the inner agreement requirement to `dIn ≤ 60`
(`s ≥ 4`) — `arity8_at_dIn60_clears_112` — a genuinely weaker statement about fewer challenges.

## ⚑ THE `hΦ` OBLIGATION — MIS-STATED HERE, then DISCHARGED (2026-07-15)

`good_card_le_of_phase_injective` takes the fiber bound `M = 1` as the HYPOTHESIS `hΦ` (the phase map
`Φ` is injective). In §8 the `m = 2` analogue is DISCHARGED from farness by `far_fiber_card` +
`wrap_fiber_le_one` over the concrete `friSetupWrapRate`. This file originally NAMED the arity-8
analogue as the `Prop` `Arity8FiberBound` and declared it the open residual, saying the discharge
needed an arity-8 RS setup (`|L| = 512`, `|κ| = 64`, RS dimension `8 → 1`) "that this tree does not
build".

**Both halves of that were wrong, in opposite directions.**

1. **The named `Prop` was FALSE, not open** (`arity8FiberBoundNaive_false`, §2). It quantified over
   every phase map `Φ` and never mentioned a far word — the farness link, which is the whole content,
   was missing — so the constant map `Φ = 0` refutes it. It named no obligation. Nothing consumed it,
   here or anywhere, so nothing was contaminated; but it was not a residual, it was a mis-statement.
2. **The real obligation DISCHARGES.** `Dregg2.Circuit.FriArityFiberDischarge` builds the arity-`2^k`
   rate-`2^(−b)` setup parametrically (so `|L| = 512`, `|κ| = 64`, dimension `8` is one instance of
   it), generalizes `far_fiber_card` to arity `n` (`far_fiber_card_arity`), and PROVES `hΦ` from
   farness at every shipped config (`phase_injective_of_far`; at the deployed arity 8,
   `arity8_phase_injective`, for `dOut ≥ 496`). The discharge fires on a concrete `503`-far word.

`good_card_le_of_phase_injective` and `arity8_good_card_le` below still CARRY `hΦ` — they are
arity-generic and know nothing of any setup, which is exactly right. The discharge is supplied where
the setup lives; `FriArityFiberDischarge.arity8_good_card_le_unconditional` is the composite with no
`hΦ` left.

`#assert_axioms` is blind to HYPOTHESES: the theorems below are kernel-clean, which does NOT mean
hypothesis-free. The `hΦ` they carry is discharged in `FriArityFiberDischarge`, not by the axiom
check.
-/

namespace Dregg2.Circuit.FriArityTransfer

open Polynomial
open Dregg2.Circuit.BabyBearFriField (BabyBear babyBearP)

variable {F : Type*} [Field F] [DecidableEq F]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-! ## §1. The phase polynomial and the arity-generic good-challenge count. -/

/-- **The phase polynomial of a point `y`.** `H m Φ y = Σ_{i<m} Φ i y · X^i` — the degree-`< m`
polynomial whose evaluation at a challenge `β` IS the arity-`m` fold of `f` at the fibre `y`:
`(H m Φ y).eval β = Σ_{i<m} Φ i y · β^i = Fold_β f (y)`. At `m = 2` this is the affine line
`E f y + β · O f y` of the mechanized model. -/
noncomputable def H (m : ℕ) (Φ : ℕ → κ → F) (y : κ) : F[X] :=
  ∑ i ∈ Finset.range m, C (Φ i y) * X ^ i

/-- The phase polynomial evaluates to the arity-`m` fold. -/
theorem H_eval (m : ℕ) (Φ : ℕ → κ → F) (y : κ) (β : F) :
    (H m Φ y).eval β = ∑ i ∈ Finset.range m, Φ i y * β ^ i := by
  simp [H, eval_finsetSum]

/-- The phase polynomial has degree `≤ m − 1`. -/
theorem H_natDegree_le (m : ℕ) (Φ : ℕ → κ → F) (y : κ) :
    (H m Φ y).natDegree ≤ m - 1 := by
  refine natDegree_sum_le_of_forall_le _ _ (fun i hi => ?_)
  refine le_trans (natDegree_C_mul_le _ _) ?_
  rw [natDegree_X_pow]
  exact Nat.le_sub_one_of_lt (Finset.mem_range.mp hi)

/-- The `j`-th coefficient of the phase polynomial is the `j`-th phase, for `j < m`. -/
theorem H_coeff (m : ℕ) (Φ : ℕ → κ → F) (y : κ) {j : ℕ} (hj : j < m) :
    (H m Φ y).coeff j = Φ j y := by
  rw [H, finsetSum_coeff]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [coeff_C_mul, coeff_X_pow, Ne.symm hij]
  · intro h
    exact absurd (Finset.mem_range.mpr hj) h

/-- **The phase polynomials of two points with DISTINCT phase vectors differ.** This is where the
`M = 1` fiber bound enters: injectivity of `Φ` makes `H y − H z` a NONZERO polynomial, so it has at
most `m − 1` roots. -/
theorem H_sub_ne_zero {m : ℕ} {Φ : ℕ → κ → F} {y z : κ}
    (h : ∃ i < m, Φ i y ≠ Φ i z) :
    H m Φ y - H m Φ z ≠ 0 := by
  obtain ⟨i, hi, hne⟩ := h
  intro hzero
  apply hne
  have := congrArg (fun p : F[X] => p.coeff i) hzero
  simpa [coeff_sub, H_coeff m Φ y hi, H_coeff m Φ z hi, sub_eq_zero] using this

/-- **THE PAIR BOUND — each pair `{y, z}` lies in at most `m − 1` good agreement sets.** For `y ≠ z`
with distinct phase vectors, a challenge `β` folding BOTH `y` and `z` to the same constant `c β` is a
root of the nonzero degree-`≤ m−1` polynomial `H y − H z`. At `m = 2` this is "at most `1`" — the
pairwise-intersection fact that powers §8's injection. At `m = 8` it is "at most `7`" — and THAT is
the entire arity-8 loss. -/
theorem pair_mem_card_le {m : ℕ} {Φ : ℕ → κ → F} {y z : κ}
    (hyz : ∃ i < m, Φ i y ≠ Φ i z)
    (Good : Finset F) (c : F → F) :
    (Good.filter (fun β => (H m Φ y).eval β = c β ∧ (H m Φ z).eval β = c β)).card ≤ m - 1 := by
  classical
  set P : F[X] := H m Φ y - H m Φ z with hP
  have hPne : P ≠ 0 := H_sub_ne_zero hyz
  have hsub : Good.filter (fun β => (H m Φ y).eval β = c β ∧ (H m Φ z).eval β = c β)
      ⊆ P.roots.toFinset := by
    intro β hβ
    simp only [Finset.mem_filter] at hβ
    obtain ⟨_, h1, h2⟩ := hβ
    rw [Multiset.mem_toFinset, mem_roots hPne]
    simp [IsRoot, hP, h1, h2]
  calc (Good.filter (fun β => (H m Φ y).eval β = c β ∧ (H m Φ z).eval β = c β)).card
      ≤ P.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card P.roots := P.roots.toFinset_card_le
    _ ≤ P.natDegree := card_roots' P
    _ ≤ m - 1 := by
        refine le_trans (natDegree_sub_le _ _) ?_
        exact max_le (H_natDegree_le m Φ y) (H_natDegree_le m Φ z)

/-- **THE ARITY-GENERIC GOOD-CHALLENGE COUNT.** Let the fibre/phase map `Φ` be INJECTIVE (the `M = 1`
far-fiber bound, §2's named obligation at arity 8). If every challenge in `Good` folds `f` to a
CONSTANT on an agreement set of size `≥ s ≥ 2`, then

  `|Good| · C(s, 2) ≤ (m − 1) · C(|κ|, 2)`.

*Proof.* Double-count the incidences `(β, {y,z})` with `{y,z} ⊆ S β`. Each `β ∈ Good` contributes
`C(|S β|, 2) ≥ C(s, 2)`. Each pair `{y,z}` is contained in `≤ m − 1` of the `S β`
(`pair_mem_card_le` — the root count of `H y − H z`). There are `C(|κ|, 2)` pairs. ∎

At `m = 2, s = 2` this is `|Good| ≤ C(|κ|, 2)` — EXACTLY `wrap_good_challenge_card_le_capacity`'s
`2016` at `|κ| = 64`. At `m = 8, s = 2` it is `|Good| ≤ 7 · 2016 = 14112`.

⚑ **Where the CONTENT is.** No `2 ≤ s` hypothesis is needed — but the bound is VACUOUS below it:
`C(0,2) = C(1,2) = 0`, so at `s < 2` it only says `0 ≤ (m−1)·C(|κ|,2)`. The content begins at
`s = 2`, which is exactly the deployed instantiation (`dIn = 62` ⇒ `|S β| ≥ 64 − 62 = 2`) — the
non-vacuous EDGE, and the same edge §8 sits on. -/
theorem good_card_le_of_phase_injective
    {m : ℕ} {Φ : ℕ → κ → F}
    (hΦ : ∀ y z : κ, y ≠ z → ∃ i < m, Φ i y ≠ Φ i z)
    (Good : Finset F) (c : F → F) {s : ℕ}
    (hS : ∀ β ∈ Good, s ≤ (Finset.univ.filter (fun y : κ => (H m Φ y).eval β = c β)).card) :
    Good.card * Nat.choose s 2 ≤ (m - 1) * Nat.choose (Fintype.card κ) 2 := by
  classical
  -- `S β` = the agreement set of the fold at challenge `β`.
  set S : F → Finset κ := fun β => Finset.univ.filter (fun y : κ => (H m Φ y).eval β = c β) with hSdef
  have hS' : ∀ β ∈ Good, s ≤ (S β).card := hS
  -- LOWER BOUND: each good β contributes `C(|S β|, 2) ≥ C(s, 2)` pairs.
  have hlow : Good.card * Nat.choose s 2
      ≤ ∑ β ∈ Good, ((S β).powersetCard 2).card := by
    have hconst : ∑ _β ∈ Good, Nat.choose s 2 = Good.card * Nat.choose s 2 := by
      rw [Finset.sum_const, smul_eq_mul]
    rw [← hconst]
    refine Finset.sum_le_sum (fun β hβ => ?_)
    rw [Finset.card_powersetCard]
    exact Nat.choose_le_choose 2 (hS' β hβ)
  -- Rewrite each `C(|S β|,2)` as a count over the 2-subsets of `κ`.
  have hrw : ∀ β ∈ Good, ((S β).powersetCard 2).card
      = (((Finset.univ : Finset κ).powersetCard 2).filter (fun P => P ⊆ S β)).card := by
    intro β _
    congr 1
    ext P
    simp only [Finset.mem_powersetCard, Finset.mem_filter, Finset.subset_univ, true_and]
    tauto
  -- SWAP the order of summation: count by PAIR instead of by challenge.
  have hswap : ∑ β ∈ Good, (((Finset.univ : Finset κ).powersetCard 2).filter (fun P => P ⊆ S β)).card
      = ∑ P ∈ (Finset.univ : Finset κ).powersetCard 2, (Good.filter (fun β => P ⊆ S β)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  -- UPPER BOUND: each pair lies in at most `m − 1` agreement sets (the root count).
  have hpair : ∀ P ∈ (Finset.univ : Finset κ).powersetCard 2,
      (Good.filter (fun β => P ⊆ S β)).card ≤ m - 1 := by
    intro P hP
    rw [Finset.mem_powersetCard] at hP
    obtain ⟨-, hP2⟩ := hP
    obtain ⟨y, z, hyz, rfl⟩ := Finset.card_eq_two.mp hP2
    refine le_trans (Finset.card_le_card ?_) (pair_mem_card_le (hΦ y z hyz) Good c)
    intro β hβ
    simp only [Finset.mem_filter] at hβ ⊢
    obtain ⟨hg, hsub⟩ := hβ
    have hy : y ∈ S β := hsub (by simp)
    have hz : z ∈ S β := hsub (by simp)
    simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and] at hy hz
    exact ⟨hg, hy, hz⟩
  calc Good.card * Nat.choose s 2
      ≤ ∑ β ∈ Good, ((S β).powersetCard 2).card := hlow
    _ = ∑ β ∈ Good, (((Finset.univ : Finset κ).powersetCard 2).filter (fun P => P ⊆ S β)).card :=
        Finset.sum_congr rfl hrw
    _ = ∑ P ∈ (Finset.univ : Finset κ).powersetCard 2, (Good.filter (fun β => P ⊆ S β)).card := hswap
    _ ≤ ∑ _P ∈ (Finset.univ : Finset κ).powersetCard 2, (m - 1) := Finset.sum_le_sum hpair
    _ = ((Finset.univ : Finset κ).powersetCard 2).card * (m - 1) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ = (m - 1) * Nat.choose (Fintype.card κ) 2 := by
        rw [Finset.card_powersetCard, Finset.card_univ, Nat.mul_comm]

/-! ## §2. The arity-8 fiber bound — the MIS-STATED obligation, its falsifier, and the arithmetic.

`good_card_le_of_phase_injective` takes `M = 1` (phase injectivity) as a hypothesis. At `m = 2` §8
DISCHARGES the analogue from farness via `far_fiber_card`. This section originally NAMED the arity-8
analogue as an open `Prop`; that `Prop` is FALSE (`arity8FiberBoundNaive_false`) because it omits the
farness link, and the REAL obligation is now PROVED in `Dregg2.Circuit.FriArityFiberDischarge`
(`arity8_phase_injective`) over the rate-`1/64` arity-8 setup (`|L| = 512`, `|κ| = 64`, dimension
`8 → 1`) that this file said the tree does not build — it does now. What survives here is the
arithmetic of the radius window, which the discharge confirms and sharpens by one. -/

/-- **`Arity8FiberBoundNaive`** — the arity-8 far-fiber obligation AS IT WAS ORIGINALLY NAMED here.
⚠ **IT IS FALSE** (`arity8FiberBoundNaive_false` below), and it is retained ONLY as the carrier of
that finding. It is used as a hypothesis by nothing, here or anywhere in the tree.

The intent was: on the rate-`1/64` arity-8 setup, a `dOut`-far word's phase map `Φ : κ → F^8` is
INJECTIVE, because a point of `F^8` lifts to the degree-`< 8` codeword `Σ aᵢXⁱ` and each fibre
contributes all `8` of its domain points to that codeword's agreement, so `8·|Φ⁻¹(a)| + dOut < 512`
forces `|Φ⁻¹(a)| ≤ 1` once `dOut ≥ 496`.

The STATEMENT below does not say that. It quantifies over EVERY `Φ` and never mentions a word, let
alone a far one — the farness link, which is the entire content of the intended claim, is missing. So
it asserts that every phase map whatsoever is injective, which the constant map refutes.

⚑ The honest reading: this obligation was not OPEN, it was MIS-STATED. `Dregg2.Circuit.
FriArityFiberDischarge.Arity8FiberBound` restates it correctly (over the real `|L| = 512` dimension-8
setup, with the farness hypothesis) and PROVES it — `arity8_phase_injective`. The `hΦ` carried by
`good_card_le_of_phase_injective` / `arity8_good_card_le` below is therefore DISCHARGED at the
deployed config; those theorems keep `hΦ` as a hypothesis because they are arity-generic, and the
discharge is supplied by the setup-specific file. -/
def Arity8FiberBoundNaive (dOut : ℕ) : Prop :=
  ∀ (Φ : ℕ → Fin (2 ^ 6) → BabyBear), 496 ≤ dOut →
    (∀ y z : Fin (2 ^ 6), y ≠ z → ∃ i < 8, Φ i y ≠ Φ i z)

/-- **THE FALSIFIER — `Arity8FiberBoundNaive` IS FALSE, at its own quoted radius `dOut = 500`.**
The constant phase map `Φ = fun _ _ => 0` has `Φ i y = Φ i z` for every `i` and every pair, so it is
not injective; the naive statement claims it is. A `Prop` that is false names no obligation — assume
it and you may conclude anything.

This is the repo's `toy_dl_not_hard` discipline applied to our own floor: a hypothesis carrier is
only honest if its negation is a concrete counterexample you have actually looked for. This one's
negation is a one-line counterexample, and the statement stood for a lane before anyone tried it. -/
theorem arity8FiberBoundNaive_false : ¬ Arity8FiberBoundNaive 500 := by
  intro h
  obtain ⟨i, -, hne⟩ := h (fun _ _ => (0 : BabyBear)) (by norm_num) 0 1 (by decide)
  exact hne rfl

/-- **THE ARITY-8 FIBER WINDOW IS NON-EMPTY** — `M = 1` needs `dOut ≥ 496` (from
`8·|Φ⁻¹| + dOut < 512` at `|Φ⁻¹| = 2`), while a word can be at most `504 = 512 − 8`-far from a
dimension-`8` RS code (interpolation through any `8` points forces agreement `≥ 8`). So the window
`496 ≤ dOut ≤ 504` where the hypothesis is BOTH forceable AND satisfiable is nonempty — the arity-8
analogue of §8's `125 + 2 = 127 < 128` non-vacuity check. `dOut = 500` (the exact scaled analogue of
§8's `125/128`, `500/512 = 125/128`) sits inside it.

⚑ The `504` upper end is one too generous: `farN` is STRICT (`> dOut` disagreements), so a word with
agreement exactly `8` is `503`-far, not `504`-far. `FriArityFiberDischarge.
arity8_fiber_window_realizable` records the REALIZABLE window `496 ≤ dOut ≤ 503`, exhibited by a
concrete `503`-far word. `dOut = 500` sits inside either way, so no number downstream moves. -/
theorem arity8_fiber_window_nonempty : 496 ≤ 500 ∧ 500 ≤ 512 - 8 := by norm_num

/-- `500/512 = 125/128` — `dOut = 500` at arity 8 is the EXACT scaled analogue of §8's near-capacity
radius `dOut = 125` on the `128`-point arity-2 domain (relative `δ ≈ 0.977`). So the arity-8 number
below is quoted at the SAME relative radius as the ~112.6 it is compared against. -/
theorem arity8_radius_matches_arity2 : (500 : ℚ) / 512 = 125 / 128 := by norm_num

/-! ## §3. THE COUNTS — arity 2 recovers §8 exactly; arity 8 costs exactly a factor `7`. -/

/-- **SANITY — the generic bound RECOVERS §8's `2016` at arity 2.** At `m = 2`, `|κ| = 64`, `s = 2`:
`|Good| · C(2,2) ≤ (2−1) · C(64,2) = 2016`. This is exactly the count
`wrap_good_challenge_card_le_capacity` proves by the direct pair-injection — the check that §1's
generalization is the RIGHT one. -/
theorem arity2_recovers_capacity_count : (2 - 1) * Nat.choose 64 2 = 2016 := by decide

/-- **THE ARITY-8 COUNT** — `(8−1) · C(64,2) = 7 · 2016 = 14112`. -/
theorem arity8_count : (8 - 1) * Nat.choose 64 2 = 14112 := by decide

/-- **THE ARITY-8 BOUND IS EXACTLY `7×` THE ARITY-2 BOUND.** The loss is the degree-`7` moment curve:
a pair of fibres can lie in `7` good agreement sets where the affine line admits only `1`. -/
theorem arity8_bound_is_seven_times_arity2 :
    (8 - 1) * Nat.choose 64 2 = 7 * ((2 - 1) * Nat.choose 64 2) := by decide

/-- **THE DEPLOYED ARITY-8 GOOD COUNT.** `good_card_le_of_phase_injective` at the deployed shape
`m = 8`, `κ = Fin (2^6)` (`|κ| = 64`), `s = 2` (the §8 inner radius `dIn = 62`: `|S β| ≥ 64 − 62 = 2`):
a word whose phase map is injective (the `Arity8FiberBound` obligation) has at most `14112` good
folding challenges. -/
theorem arity8_good_card_le {Φ : ℕ → Fin (2 ^ 6) → BabyBear}
    (hΦ : ∀ y z : Fin (2 ^ 6), y ≠ z → ∃ i < 8, Φ i y ≠ Φ i z)
    (Good : Finset BabyBear) (c : BabyBear → BabyBear)
    (hS : ∀ β ∈ Good, 2 ≤ (Finset.univ.filter (fun y : Fin (2 ^ 6) =>
        (H 8 Φ y).eval β = c β)).card) :
    Good.card ≤ 14112 := by
  have h := good_card_le_of_phase_injective hΦ Good c (s := 2) hS
  have hc : Fintype.card (Fin (2 ^ 6)) = 64 := by simp
  rw [hc] at h
  simpa [Nat.choose_two_right] using h

/-! ## §4. THE DEPLOYED PER-FOLD SOUNDNESS AT ARITY 8 — and the honest comparison to ~112.6. -/

/-- **THE DEPLOYED ARITY-8 PER-FOLD SOUNDNESS.** The arity-8 good count `≤ 14112` is
FIELD-INDEPENDENT (the double-count lands in the unordered pairs of the `64`-point folded domain `κ`,
not in the challenge field), so it holds when challenges are drawn from the deployed quartic
extension `F = BabyBear⁴`, `|F| = babyBearP⁴ ≈ 2^123.6`. The per-fold error is then
`|Good| / |F| ≤ 14112 / babyBearP⁴ < 2⁻¹⁰⁹`.

**This is the honest DEPLOYED number: ~109.84 bits — BELOW the ~112.6 posture**, which is proved for
a 2-to-1 fold the deployed prover does not run. -/
theorem arity8_perFold_soundness (Good : Finset BabyBear) (hGood : Good.card ≤ 14112) :
    (Good.card : ℝ) / (babyBearP : ℝ) ^ 4 < 1 / 2 ^ 109 := by
  have hcR : (Good.card : ℝ) ≤ 14112 := by exact_mod_cast hGood
  have hpval : (babyBearP : ℝ) = 2013265921 := by norm_num [babyBearP]
  rw [hpval]
  have hden : (0 : ℝ) < (2013265921 : ℝ) ^ 4 := by norm_num
  have h2 : (0 : ℝ) < (2 : ℝ) ^ 109 := by positivity
  rw [div_lt_div_iff₀ hden h2, one_mul]
  have key : (14112 : ℝ) * 2 ^ 109 < (2013265921 : ℝ) ^ 4 := by norm_num
  nlinarith [hcR, h2, key]

/-- **THE EXACT ARITY-8 SOUNDNESS INTERVAL — `2⁻¹¹⁰ < 14112/babyBearP⁴ < 2⁻¹⁰⁹`.** The deployed
arity-8 per-fold error is strictly between `2⁻¹¹⁰` and `2⁻¹⁰⁹` (`≈ 2⁻¹⁰⁹·⁸⁴`): the proven guarantee is
`≥ 109` bits (the `2⁻¹⁰⁹` upper bound), NOT a rounded `110`. Compare
`wrap_perFold_soundness_capacity_interval`'s `2016·2¹¹² < babyBearP⁴ < 2016·2¹¹³` (`~112.65`). -/
theorem arity8_perFold_soundness_interval :
    14112 * 2 ^ 109 < babyBearP ^ 4 ∧ babyBearP ^ 4 < 14112 * 2 ^ 110 := by
  refine ⟨?_, ?_⟩ <;> norm_num [babyBearP]

/-- **THE ARITY-8 POSTURE IS STRICTLY BELOW THE ARITY-2 POSTURE — a BOTH-TRUTH tooth.** The deployed
arity-8 per-fold error `14112/babyBearP⁴` is strictly LARGER than the modeled arity-2 error
`2016/babyBearP⁴`; it is NOT below `2⁻¹¹²`. So the standing ~112.6 does NOT hold at the deployed
arity 8 by this method — the transfer is unsound, and this is the falsifier. -/
theorem arity8_error_not_lt_2e112 :
    ¬ (14112 : ℝ) / (babyBearP : ℝ) ^ 4 < 1 / 2 ^ 112 := by
  rw [not_lt]
  have hpval : (babyBearP : ℝ) = 2013265921 := by norm_num [babyBearP]
  rw [hpval, div_le_div_iff₀ (by positivity) (by norm_num)]
  norm_num

/-- **THE LOSS IS EXACTLY A FACTOR OF `7` (`log₂ 7 ≈ 2.807` bits).** `14112 = 7 · 2016`. -/
theorem arity8_loses_exactly_factor_seven : (14112 : ℕ) = 7 * 2016 := by decide

/-- **RECOVERING ~112.6 AT ARITY 8 COSTS A STRICTLY STRONGER INNER RADIUS.** At `dIn = 60`
(`s = 4`, so `C(4,2) = 6`) the generic bound gives `|Good| ≤ 7·2016/6 = 2352`, and
`2352/babyBearP⁴ < 2⁻¹¹²` — clearing the ~112.6 bar. So arity-8 folding reaches the posture only for
the WEAKER statement that quantifies over challenges folding to within `60` (not `62`) of the code:
fewer challenges are "good", so bounding them is a lesser claim. This is the honest price. -/
theorem arity8_at_dIn60_clears_112 :
    (8 - 1) * Nat.choose 64 2 / Nat.choose 4 2 = 2352 ∧
      (2352 : ℝ) / (babyBearP : ℝ) ^ 4 < 1 / 2 ^ 112 := by
  refine ⟨by decide, ?_⟩
  have hpval : (babyBearP : ℝ) = 2013265921 := by norm_num [babyBearP]
  rw [hpval, div_lt_div_iff₀ (by norm_num) (by positivity), one_mul]
  norm_num

/-! ## §5. Axiom hygiene.

Every theorem below is kernel-clean. `#assert_axioms` is BLIND TO HYPOTHESES: kernel-clean does NOT
mean hypothesis-free. `good_card_le_of_phase_injective` / `arity8_good_card_le` carry the phase-
injectivity (`M = 1`) hypothesis `hΦ` — correctly, since they are arity-generic and mention no setup.
`hΦ` is DISCHARGED from farness at every shipped config in `Dregg2.Circuit.FriArityFiberDischarge`
(`phase_injective_of_far`; `arity8_phase_injective` at the deployed arity 8), whose
`arity8_good_card_le_unconditional` is the composite carrying no `hΦ`. The `Prop` this file once
named as the open residual is FALSE and is retained only as the carrier of that finding
(`arity8FiberBoundNaive_false`). -/

#assert_axioms arity8FiberBoundNaive_false
#assert_axioms H_eval
#assert_axioms H_natDegree_le
#assert_axioms H_coeff
#assert_axioms H_sub_ne_zero
#assert_axioms pair_mem_card_le
#assert_axioms good_card_le_of_phase_injective
#assert_axioms arity8_fiber_window_nonempty
#assert_axioms arity8_radius_matches_arity2
#assert_axioms arity2_recovers_capacity_count
#assert_axioms arity8_count
#assert_axioms arity8_bound_is_seven_times_arity2
#assert_axioms arity8_good_card_le
#assert_axioms arity8_perFold_soundness
#assert_axioms arity8_perFold_soundness_interval
#assert_axioms arity8_error_not_lt_2e112
#assert_axioms arity8_loses_exactly_factor_seven
#assert_axioms arity8_at_dIn60_clears_112

end Dregg2.Circuit.FriArityTransfer

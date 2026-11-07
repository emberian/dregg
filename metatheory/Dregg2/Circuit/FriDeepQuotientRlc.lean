/-
# `Dregg2.Circuit.FriDeepQuotientRlc` — L5·R4b sub-piece 1: the DEPLOYED DEEP-quotient α-RLC
input reduction, MODELED.

## What this file is

`FriDecodedTraceWitness.lean:450` (`DecodedLdtLink`) names three sub-pieces that close the DEEP-ALI
residual. Sub-piece 1 is "a Lean model of the deployed DEEP quotient — the FRI input word IS the
α-RLC of the per-column quotients". `FriBatchedOracle.lean:50-57` and
`DeployedTraceExtract.lean:414-419` both name that reduction as DELIBERATELY unmodeled. This file
models it.

## The deployed object (verbatim, rev `82cfad73`, `fri/src/verifier.rs:617-640`)

```rust
let (alpha_pow, ro) = reduced_openings.entry(log_height).or_insert((Challenge::ONE, Challenge::ZERO));
for (point, (z, ps_at_z)) in mat_points_and_values.iter().enumerate() {
    let quotient = (*z - x).inverse();
    for (&p_at_x, &p_at_z) in mat_opening.iter().zip(ps_at_z.iter()) {
        *ro += *alpha_pow * (p_at_z - p_at_x) * quotient;
        *alpha_pow *= alpha;
    }
}
```

so the FRI input word at domain point `x` is `ro(x) = Σ_j α^j · (p_j(z) − p_j(x)) · (z − x)⁻¹`.

**TYPES (checked in the source, not assumed).** `x : Val` (`= Val::GENERATOR *
two_adic_generator(log_height)^rev_index`, `:614-615`) is BASE field; `p_at_x : Val` (an element of
`mat_opening`, the Merkle-opened row) is BASE field; `z`, `p_at_z`, `alpha`, `alpha_pow`, `ro`,
`quotient` are all `Challenge` — the DEGREE-4 EXTENSION. So the committed base-field value becomes
extension-valued at the SUBTRACTION `p_at_z - p_at_x`, i.e. BEFORE any challenge multiplies it, and
the FRI input word is an EXTENSION-valued word over a BASE-field evaluation domain. This file is
therefore typed over `[Field F] [Field E] [Algebra F E]` with the committed matrix over `F` and the
reduced word over `E`; `E := F` (the trivial algebra) recovers the in-tree single-field shape.

## What is PROVEN here (no `sorry`, no `axiom`, no vacuous statement)

* §0 **the imperative loop IS the closed form** — `reduceOpening_eq`: the deployed mutable
  `(alpha_pow, ro)` fold over the opened row equals `(α^len, Σ_i α^i · tᵢ)`. The model is the
  deployed loop, not a formula that resembles it.
* §1 **the factor theorem, deployed-side** — `deepQuot p z := p /ₘ (X − C z)` is a genuine
  polynomial with `p = C (p.eval z) + (X − C z) · deepQuot p z`, `natDegree` DROPS by one
  (`deepQuot_natDegree_lt`: `natDegree p < k`, `2 ≤ k` ⟹ `natDegree (deepQuot p z) < k − 1`), and
  its evaluation at any `x ≠ z` is EXACTLY the deployed division
  (`deepQuot_eval_deployed`: `= (p.eval z − p.eval x) * (z − x)⁻¹`). This is what makes the deployed
  `.inverse()` well-defined as a low-degree object.
* §2 **the RLC** — `rlcQuotPoly`, degree `< k − 1`, and `friInputWord_eq_evalVec`: when every
  committed column IS a codeword and the claimed OOD values are the honest ones, the deployed input
  word IS `evalVec` of a single `natDegree < k − 1` polynomial — so it is a CODEWORD of the
  degree-`< k−1` RS code on the (embedded) domain (`friInputWord_mem_rsCode`).
* §3 **the perturbation bound** — `friInputWord_closeN`: if every column is only `d`-CLOSE to its
  codeword (the `ColsClose` input the deployed decode actually has), the input word is
  `(numCols · d)`-close to the quotient code. Union bound over the columns; no CA needed.
* §4 **the per-column DEEP soundness fact** — `deepQuotWord_agree_card_le` /
  `oodValue_correct_of_close`: if the claimed OOD value `v ≠ P.eval z`, the column's quotient word
  agrees with EVERY degree-`< D` codeword in at most `m` places (`m ≥ max (natDegree P) D`), so a
  quotient word inside radius `e` with `e + m < n` FORCES `v = P.eval z`. This is the real content
  of "DEEP quotient in the decoding radius ⟹ the opened value is the true one", per column.
* §5 **the CA consumption point, and what it buys** — `RlcDistributes` (§5) is the ONE named
  hypothesis; `oodValues_correct_of_rlcDistributes` derives, FROM IT AND NOTHING ELSE, that EVERY
  claimed OOD value equals the decoded column's value at `z`. That is sub-piece 2's conclusion,
  conditional on exactly one thing. The hypothesis SHAPE is not a black box:
  `rlcDistributes_one_column` PROVES it at `numCols = 1` (there the RLC is the column itself), so
  what CA supplies is precisely the multi-column strengthening at a nontrivial list size.
* §6 **firing + teeth** — a real `ZMod 17` instance: 4-point domain (the 4th roots of unity),
  out-of-domain `z = 3`, columns `X² + 2X + 3` and `X + 1`. `deepQuot p₀ 3 = X + 5` as a GENUINE
  polynomial identity (`fire_deepQuot0`); its evaluation matches the deployed
  `(p(z) − p(x))·(z − x)⁻¹` numerically (`fire_deepQuot_eval_deployed`, both `= 9`); the 2-column
  α-RLC at `α = 2` computes `11` and the deployed imperative loop returns the same `(4, 11)`
  (`fire_friInputWord` / `fire_reduceOpening`); §2's membership theorem FIRES on the instance
  (`fire_friInputWord_mem_rsCode`), and so does the §5 keystone — `fire_oodValues_correct` shows
  its ENTIRE hypothesis bundle is inhabited (CA discharged there by `rlcDistributes_one_column`),
  so it is not true-by-emptiness. TEETH: `fire_wrong_ood_not_close` — a WRONG opened value `0`
  in place of the true `p₀(3) = 1` puts the quotient word outside radius `1`, so §4 bites; and
  `rlc_single_challenge_no_distribution` exhibits two words whose RLC at `α = 1` is the ZERO
  codeword while the first is not in the code at all — the single-challenge converse is FALSE, which
  is exactly why `RlcDistributes` needs a large `Good` set.

## What is NOT proven — the ONE named hypothesis (`RlcDistributes`, §5)

`RlcDistributes code d L agree u`: if MORE than `L` challenges `α` make the α-RLC
`Σ_j α^j · u_j` `d`-close to `code`, then there are codewords `g_j ∈ code` and a COMMON set of
`≥ agree` domain points on which every `u_j` agrees with `g_j` simultaneously. This is BCIKS20
correlated agreement for the power-RLC family, and it is stated in EXACTLY the shape of the in-tree
affine-line primitive `FriCorrelatedAgreementSharp.CorrelatedAgreementLineAt`
(`FriCorrelatedAgreementSharp.lean:106`) so the sibling CA formalization can discharge it. It is
NOT proven here, NOT axiomatized, and nothing in this file assumes it — it appears only as an
explicit hypothesis of §5's theorems. Going from "the batched RLC word is close" back to "every
column's quotient word is close" is the ONLY step of the DEEP argument this file does not prove,
and it is the exact step correlated agreement exists to supply.

## Honest scope notes (do not read this file as more than it is)

1. **Extension-typed word vs base-field in-tree code.** The deployed input word is `Challenge`
   (degree-4 extension) valued, and this file types it that way. The in-tree deployed FRI instance
   `friSetupDeployed.C = rsCode (pR 8 (2^21) omega24) (2^18 * 8)` is a BABYBEAR (base-field)
   submodule, and `DecodedLdtLink` consumes `MatrixOracle (Fin (8*2^21)) numCols BabyBear`. So
   wiring §2–§5 into `DecodedLdtLink` needs an EXTENSION-typed FRI code object that does not exist
   in the tree yet. That is a real, named gap between this model and the current L5 assembly — this
   file does not paper over it, and no theorem here claims a connection to `friSetupDeployed`.
2. **One matrix, one opening point.** The deployed loop iterates `mat_points_and_values` (several
   OOD points `z` per matrix) and several matrices per batch, with ONE running `alpha_pow` across
   all of them. This file models the inner two loops (one matrix, one `z`, all its columns) —
   the shape the DEEP-ALI argument consumes. The outer concatenation is a further (mechanical)
   generalization: `reduceOpening` already takes an arbitrary term LIST, so the multi-point case is
   the same fold on a longer list, but no theorem below states it.
3. **Merkle binding is assumed elsewhere.** `p_at_x` is the OPENED value; that it equals the
   committed matrix entry is `verify_batch` / the `Poseidon2SpongeCR` floor, not this file.

Additive new file; imports read-only. Sorry-free; no `axiom`; `#assert_all_clean` on every keystone.
-/
import Dregg2.Circuit.FriBatchedOracle
import Dregg2.Circuit.FriCloseNUniqueDecode
import Dregg2.Tactics

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Dregg2.Circuit.FriDeepQuotientRlc

open Dregg2.Circuit.FriSoundness (closeN disagree mem_disagree disagree_eq_empty_iff)
open Dregg2.Circuit.FriBatchedOracle (MatrixOracle)
open Dregg2.Circuit.RsUniqueDecoding (evalVec)
open Dregg2.Circuit.FriDeployedRateInstance (rsCode mem_rsCode)
open Dregg2.Circuit.FriCloseNUniqueDecode (mem_rsCode_iff_lowDegree_evalVec)

/-! ## §0 — The deployed reduction LOOP, and its closed form.

The Rust is imperative: a mutable `(alpha_pow, ro)` pair folded over the opened row. We model that
fold LITERALLY (`roStep`/`reduceOpening`) and prove it equals the geometric-weighted sum, so every
later theorem about `Σ_j α^j · tⱼ` is a theorem about the deployed loop. -/

section Loop

variable {E : Type*} [Field E]

/-- ONE iteration of the deployed inner loop: `*ro += *alpha_pow * t; *alpha_pow *= alpha`, on the
state `(alpha_pow, ro)`. -/
def roStep (α : E) (st : E × E) (t : E) : E × E := (st.1 * α, st.2 + st.1 * t)

/-- The deployed reduction: fold `roStep` over the row's per-column terms from the deployed initial
state `(Challenge::ONE, Challenge::ZERO)` (`verifier.rs:617-619`). -/
def reduceOpening (α : E) (ts : List E) : E × E := ts.foldl (roStep α) (1, 0)

/-- The loop's state after folding from an ARBITRARY start (the generalization induction needs). -/
theorem roStep_foldl (α : E) : ∀ (ts : List E) (a r : E),
    ts.foldl (roStep α) (a, r)
      = (a * α ^ ts.length, r + ∑ i ∈ Finset.range ts.length, a * α ^ i * ts.getD i 0) := by
  intro ts
  induction ts with
  | nil => intro a r; simp
  | cons t ts ih =>
    intro a r
    have hstep : roStep α (a, r) t = (a * α, r + a * t) := rfl
    rw [List.foldl_cons, hstep, ih]
    have hlen : (t :: ts).length = ts.length + 1 := rfl
    refine Prod.ext ?_ ?_
    · simp [hlen, pow_succ, mul_comm, mul_assoc, mul_left_comm]
    · simp only [hlen]
      rw [Finset.sum_range_succ' (fun i => a * α ^ i * (t :: ts).getD i 0) ts.length]
      have hshift : ∀ i, (t :: ts).getD (i + 1) 0 = ts.getD i 0 := by
        intro i; simp [List.getD]
      have h0 : (t :: ts).getD 0 0 = t := by simp [List.getD]
      simp only [hshift, h0]
      have : ∀ i ∈ Finset.range ts.length,
          a * α * α ^ i * ts.getD i 0 = a * α ^ (i + 1) * ts.getD i 0 := by
        intro i _; ring
      rw [Finset.sum_congr rfl this]
      ring

/-- **The deployed loop IS the geometric-weighted sum.** `ro` ends at `Σ_i α^i · tᵢ` and
`alpha_pow` at `α^{#terms}` (the latter is what carries the power across matrices in the deployed
outer loop). -/
theorem reduceOpening_eq (α : E) (ts : List E) :
    reduceOpening α ts
      = (α ^ ts.length, ∑ i ∈ Finset.range ts.length, α ^ i * ts.getD i 0) := by
  rw [reduceOpening, roStep_foldl]
  simp

/-- The `Fin c` (one matrix row) form of the closed loop: the reduced opening of a row of `c`
per-column terms. -/
theorem reduceOpening_ofFn {c : ℕ} (α : E) (t : Fin c → E) :
    (reduceOpening α (List.ofFn t)).2 = ∑ j : Fin c, α ^ (j : ℕ) * t j := by
  rw [reduceOpening_eq]
  simp only [List.length_ofFn]
  rw [← Fin.sum_univ_eq_sum_range (fun i => α ^ i * (List.ofFn t).getD i 0) c]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  congr 1
  simp

end Loop

/-! ## §1 — The DEEP quotient of ONE polynomial at an out-of-domain point.

`deepQuot p z` is the polynomial `(p(X) − p(z))/(X − z)`. The factor theorem is what makes the
deployed `.inverse()` legitimate: the division is EXACT, so the quotient is a genuine polynomial of
one lower degree, and its evaluation at any in-domain `x` (necessarily `≠ z`, since `z` is
out-of-domain) is exactly the field division the verifier computes. -/

section Quotient

variable {K : Type*} [Field K]

/-- **The DEEP quotient** `(p(X) − p(z))/(X − z)`, as division by the MONIC `X − C z` (so it is
literally a polynomial, not a rational function). -/
noncomputable def deepQuot (p : Polynomial K) (z : K) : Polynomial K :=
  p /ₘ (Polynomial.X - Polynomial.C z)

/-- **The factor theorem, in the exact form the verifier's division needs**:
`p = C (p.eval z) + (X − C z) · deepQuot p z`. -/
theorem deepQuot_spec (p : Polynomial K) (z : K) :
    p = Polynomial.C (p.eval z) + (Polynomial.X - Polynomial.C z) * deepQuot p z := by
  conv_lhs => rw [← Polynomial.modByMonic_add_div p (Polynomial.X - Polynomial.C z)]
  rw [Polynomial.modByMonic_X_sub_C_eq_C_eval, deepQuot]

/-- The evaluation form: `p(x) = p(z) + (x − z)·q(x)` for every `x`. -/
theorem deepQuot_eval_spec (p : Polynomial K) (z x : K) :
    p.eval x = p.eval z + (x - z) * (deepQuot p z).eval x := by
  conv_lhs => rw [deepQuot_spec p z]
  simp

/-- **The DEEP quotient evaluates to the division** — mathematician's orientation. -/
theorem deepQuot_eval {p : Polynomial K} {z x : K} (hx : x ≠ z) :
    (deepQuot p z).eval x = (p.eval x - p.eval z) / (x - z) := by
  have hne : x - z ≠ 0 := sub_ne_zero_of_ne hx
  have hspec := deepQuot_eval_spec p z x
  rw [eq_div_iff hne]
  linear_combination -hspec

/-- **The DEEP quotient evaluates to the DEPLOYED division** — the verbatim orientation of
`fri/src/verifier.rs:624,638`: `quotient = (z − x).inverse()` and the accumulated term is
`(p_at_z − p_at_x) * quotient`, i.e. `(p(z) − p(x)) · (z − x)⁻¹`. Equal to `deepQuot`'s value, so
the deployed per-column contribution IS a low-degree evaluation. -/
theorem deepQuot_eval_deployed {p : Polynomial K} {z x : K} (hx : x ≠ z) :
    (p.eval z - p.eval x) * (z - x)⁻¹ = (deepQuot p z).eval x := by
  have hne : z - x ≠ 0 := sub_ne_zero_of_ne (Ne.symm hx)
  have hspec := deepQuot_eval_spec p z x
  rw [← div_eq_mul_inv, div_eq_iff hne]
  linear_combination -hspec

/-- **The degree DROPS by one.** `natDegree (p /ₘ (X − C z)) = natDegree p − 1` — so a
degree-`< k` column produces a degree-`< k−1` quotient (`2 ≤ k` is needed only because `k − 1`
is ℕ-subtraction: at `k = 1` every `p` is constant and the quotient is `0`, whose `natDegree` is
`0`, and `natDegree < 0` is unsatisfiable). -/
theorem deepQuot_natDegree (p : Polynomial K) (z : K) :
    (deepQuot p z).natDegree = p.natDegree - 1 := by
  rw [deepQuot, Polynomial.natDegree_divByMonic p (Polynomial.monic_X_sub_C z),
    Polynomial.natDegree_X_sub_C]

theorem deepQuot_natDegree_lt {p : Polynomial K} {z : K} {k : ℕ}
    (hp : p.natDegree < k) (hk : 2 ≤ k) : (deepQuot p z).natDegree < k - 1 := by
  rw [deepQuot_natDegree]; omega

/-- **Uniqueness of the quotient** — exhibiting ONE `q` with `p = C (p.eval z) + (X − C z)·q` PINS
`deepQuot p z = q`. (What lets §6 name the quotient of a concrete polynomial.) -/
theorem deepQuot_eq_of_spec {p q : Polynomial K} {z : K}
    (h : p = Polynomial.C (p.eval z) + (Polynomial.X - Polynomial.C z) * q) :
    deepQuot p z = q := by
  refine (Polynomial.div_modByMonic_unique q (Polynomial.C (p.eval z))
    (Polynomial.monic_X_sub_C z) ⟨h.symm, ?_⟩).1
  refine lt_of_le_of_lt Polynomial.degree_C_le ?_
  rw [Polynomial.degree_X_sub_C]
  exact WithBot.coe_lt_coe.mpr Nat.zero_lt_one

end Quotient

/-! ## §2 — The deployed FRI INPUT WORD: the α-RLC of the per-column DEEP quotients.

Typed as the deployed verifier types it: the committed matrix is over the BASE field `F`, the OOD
values / challenge / reduced opening are over the EXTENSION `E`, and the base-field opened value is
embedded at the subtraction (`p_at_z - p_at_x`), before any challenge multiplies it. -/

section Rlc

variable {F E : Type*} [Field F] [Field E] [Algebra F E]
variable {ι : Type*} {c : ℕ}

/-- ONE deployed per-column contribution BEFORE the `alpha_pow` weight:
`(p_at_z − p_at_x) * quotient` with `quotient = (z − x)⁻¹` (`verifier.rs:624,638`). -/
def deepTerm (z px vx vz : E) : E := (vz - vx) * (z - px)⁻¹

/-- The `j`-th committed column's DEEP-quotient WORD over the evaluation domain, as the verifier
forms it at each queried point: the base-field opened entry `M x j` embedded into the extension,
subtracted from the CLAIMED OOD value `vz j`, over `z − x`. -/
noncomputable def colQuotWord (pts : ι → F) (z : E) (M : MatrixOracle ι c F) (vz : Fin c → E)
    (j : Fin c) : ι → E :=
  fun x => deepTerm z (algebraMap F E (pts x)) (algebraMap F E (M.row x j)) (vz j)

/-- **THE DEPLOYED FRI INPUT WORD** (`reduced_openings`, as a function of the query's domain
point): the α-random-linear-combination of the per-column DEEP quotients of the opened row. -/
noncomputable def friInputWord (pts : ι → F) (α z : E) (M : MatrixOracle ι c F)
    (vz : Fin c → E) : ι → E :=
  fun x => ∑ j : Fin c, α ^ (j : ℕ) * colQuotWord pts z M vz j x

/-- **FAITHFULNESS TO THE DEPLOYED LOOP**: the input word's value at a query point is EXACTLY what
the deployed mutable `(alpha_pow, ro)` fold over that opened row returns. The closed form used
throughout is the loop, not a lookalike. -/
theorem friInputWord_eq_loop (pts : ι → F) (α z : E) (M : MatrixOracle ι c F)
    (vz : Fin c → E) (x : ι) :
    friInputWord pts α z M vz x
      = (reduceOpening α (List.ofFn fun j =>
          deepTerm z (algebraMap F E (pts x)) (algebraMap F E (M.row x j)) (vz j))).2 :=
  (reduceOpening_ofFn α _).symm

/-- Embedding commutes with evaluation: the base-field opened value, embedded, IS the mapped
polynomial evaluated at the embedded domain point. (The bridge that makes the mixed-typing of the
deployed loop coherent.) -/
theorem algebraMap_eval (p : Polynomial F) (a : F) :
    algebraMap F E (p.eval a) = (p.map (algebraMap F E)).eval (algebraMap F E a) := by
  rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]

/-- The α-RLC of the per-column DEEP quotient POLYNOMIALS — the low-degree object the input word
is claimed to be. -/
noncomputable def rlcQuotPoly (α z : E) (P : Fin c → Polynomial E) : Polynomial E :=
  ∑ j : Fin c, Polynomial.C (α ^ (j : ℕ)) * deepQuot (P j) z

/-- **RLC DEGREE**: the α-RLC of `c` DEEP quotients of degree-`< k` columns has degree `< k − 1`,
for ANY number of columns and ANY challenge. So the deployed FRI input word is claimed to lie in
the degree-`< k−1` code — one degree below the committed columns. -/
theorem rlcQuotPoly_natDegree_lt {k : ℕ} {α z : E} {P : Fin c → Polynomial E}
    (hP : ∀ j, (P j).natDegree < k) (hk : 2 ≤ k) :
    (rlcQuotPoly α z P).natDegree < k - 1 := by
  have hle : (rlcQuotPoly α z P).natDegree ≤ k - 2 := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun j _ => ?_)
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    have := deepQuot_natDegree (P j) z
    have hj := hP j
    omega
  omega

/-- **THE IDENTIFICATION (completeness): when every committed column IS a codeword and the claimed
OOD values are the HONEST ones, the deployed FRI input word IS the evaluation of a single
polynomial** — `rlcQuotPoly` on the embedded evaluation domain. This is the theorem that makes the
deployed `.inverse()`-per-query word a codeword-shaped object. -/
theorem friInputWord_eq_evalVec {n : ℕ} (pts : Fin n → F) (α z : E)
    (M : MatrixOracle (Fin n) c F) (vz : Fin c → E) (p : Fin c → Polynomial F)
    (hz : ∀ x, algebraMap F E (pts x) ≠ z)
    (hcol : ∀ j, M.col j = evalVec pts (p j))
    (hood : ∀ j, vz j = ((p j).map (algebraMap F E)).eval z) :
    friInputWord pts α z M vz
      = evalVec (fun x => algebraMap F E (pts x))
          (rlcQuotPoly α z (fun j => (p j).map (algebraMap F E))) := by
  funext x
  have hentry : ∀ j, algebraMap F E (M.row x j)
      = ((p j).map (algebraMap F E)).eval (algebraMap F E (pts x)) := by
    intro j
    have hrow : M.row x j = (p j).eval (pts x) := congrFun (hcol j) x
    rw [hrow, algebraMap_eval]
  simp only [friInputWord, colQuotWord, deepTerm, evalVec, rlcQuotPoly,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [hentry j, hood j, deepQuot_eval_deployed (hz x)]

/-- **The input word is a CODEWORD of the degree-`< k−1` RS code** on the embedded domain (the
`friInputWord_eq_evalVec` hypotheses). -/
theorem friInputWord_mem_rsCode [DecidableEq E] {n k : ℕ} (pts : Fin n → F) (α z : E)
    (M : MatrixOracle (Fin n) c F) (vz : Fin c → E) (p : Fin c → Polynomial F)
    (hz : ∀ x, algebraMap F E (pts x) ≠ z)
    (hcol : ∀ j, M.col j = evalVec pts (p j))
    (hood : ∀ j, vz j = ((p j).map (algebraMap F E)).eval z)
    (hdeg : ∀ j, (p j).natDegree < k) (hk : 2 ≤ k) :
    friInputWord pts α z M vz ∈ rsCode (fun x => algebraMap F E (pts x)) (k - 1) := by
  refine (mem_rsCode_iff_lowDegree_evalVec (by omega)).mpr
    ⟨rlcQuotPoly α z (fun j => (p j).map (algebraMap F E)), ?_, ?_⟩
  · exact rlcQuotPoly_natDegree_lt
      (fun j => lt_of_le_of_lt (Polynomial.natDegree_map_le) (hdeg j)) hk
  · exact friInputWord_eq_evalVec pts α z M vz p hz hcol hood

end Rlc

/-! ## §3 — Perturbation: the input word under `ColsClose`, not exact membership.

The deployed decode never has "every column IS a codeword"; it has `MatrixOracle.ColsClose` —
every column `d`-close. The RLC is a POINTWISE functional of the opened row, so a disagreement of
the input word forces a disagreement in some column: a union bound gives the input word
`(numCols · d)`-close. No correlated agreement is used or needed for this direction. -/

section Perturb

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [DecidableEq E] [DecidableEq F]
variable {n c : ℕ}

/-- The input word can only disagree where some COLUMN disagrees (the RLC is pointwise in the
opened row). -/
theorem disagree_friInputWord_subset (pts : Fin n → F) (α z : E)
    (M N : MatrixOracle (Fin n) c F) (vz : Fin c → E) :
    disagree (friInputWord pts α z M vz) (friInputWord pts α z N vz)
      ⊆ Finset.univ.biUnion (fun j : Fin c => disagree (M.col j) (N.col j)) := by
  intro x hx
  rw [mem_disagree] at hx
  by_contra hcon
  refine hx ?_
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, not_exists] at hcon
  have hcols : ∀ j, M.row x j = N.row x j := by
    intro j
    by_contra h
    exact hcon j (mem_disagree.mpr h)
  simp only [friInputWord, colQuotWord]
  exact Finset.sum_congr rfl (fun j _ => by rw [hcols j])

/-- The union bound, as cardinalities. -/
theorem friInputWord_disagree_card_le (pts : Fin n → F) (α z : E)
    (M N : MatrixOracle (Fin n) c F) (vz : Fin c → E) :
    (disagree (friInputWord pts α z M vz) (friInputWord pts α z N vz)).card
      ≤ ∑ j : Fin c, (disagree (M.col j) (N.col j)).card :=
  le_trans (Finset.card_le_card (disagree_friInputWord_subset pts α z M N vz))
    (Finset.card_biUnion_le)

/-- **THE `ColsClose` FORM OF THE IDENTIFICATION.** With every committed column `d`-close to a
degree-`< k` codeword and the OOD values honest for THOSE codewords, the deployed FRI input word
is `(numCols · d)`-close to the degree-`< k−1` RS code. This is the honest completeness statement
at the radius the deployed decode actually operates at. -/
theorem friInputWord_closeN {k d : ℕ} (pts : Fin n → F) (α z : E)
    (M : MatrixOracle (Fin n) c F) (vz : Fin c → E) (p : Fin c → Polynomial F)
    (hz : ∀ x, algebraMap F E (pts x) ≠ z)
    (hclose : ∀ j, (disagree (M.col j) (evalVec pts (p j))).card ≤ d)
    (hood : ∀ j, vz j = ((p j).map (algebraMap F E)).eval z)
    (hdeg : ∀ j, (p j).natDegree < k) (hk : 2 ≤ k) :
    closeN (rsCode (fun x => algebraMap F E (pts x)) (k - 1)) (c * d)
      (friInputWord pts α z M vz) := by
  refine ⟨friInputWord pts α z (fun x j => (p j).eval (pts x)) vz,
    friInputWord_mem_rsCode pts α z _ vz p hz (fun _ => rfl) hood hdeg hk, ?_⟩
  refine le_trans (friInputWord_disagree_card_le pts α z M _ vz) ?_
  refine le_trans (Finset.sum_le_sum (fun j _ => hclose j)) ?_
  simp [Finset.sum_const]

end Perturb

/-! ## §4 — The per-column DEEP soundness fact: a WRONG opened value is FAR.

This is the content of "DEEP quotient inside the decoding radius ⟹ the opened value is the true
one", for ONE column. It is a theorem here (no correlated agreement involved): if the claimed OOD
value `v` differs from `P(z)`, then `x ↦ (v − P(x))/(z − x)` agrees with EVERY low-degree word in
at most `m` points, because agreement makes `x` a root of the nonzero degree-`≤ m` polynomial
`C v − P + (X − C z)·q` (nonzero because it evaluates to `v − P(z) ≠ 0` at `z`). -/

section Far

variable {K : Type*} [Field K] [DecidableEq K]

/-- **A WRONG claimed OOD value bounds the AGREEMENT of the column's DEEP-quotient word with every
degree-`≤ m−1` word by `m`.** -/
theorem deepQuotWord_agree_card_le {n m : ℕ} {pts : Fin n → K} (hinj : Function.Injective pts)
    {z v : K} (hz : ∀ x, pts x ≠ z) {P q : Polynomial K}
    (hP : P.natDegree ≤ m) (hq : q.natDegree + 1 ≤ m) (hv : v ≠ P.eval z) :
    (Finset.univ.filter (fun x : Fin n =>
        (v - P.eval (pts x)) * (z - pts x)⁻¹ = q.eval (pts x))).card ≤ m := by
  classical
  set R : Polynomial K :=
    Polynomial.C v - P + (Polynomial.X - Polynomial.C z) * q with hR
  -- `R` is NONZERO: it evaluates to `v − P(z) ≠ 0` at the out-of-domain point.
  have hRz : R.eval z = v - P.eval z := by simp [hR]
  have hR0 : R ≠ 0 := by
    intro h0
    rw [h0] at hRz
    simp only [Polynomial.eval_zero] at hRz
    exact hv (by linear_combination -hRz)
  -- degree bound
  have hdeg : R.natDegree ≤ m := by
    refine le_trans (Polynomial.natDegree_add_le _ _) ?_
    refine max_le (le_trans (Polynomial.natDegree_sub_le _ _) ?_) ?_
    · exact max_le (by simp) hP
    · refine le_trans (Polynomial.natDegree_mul_le) ?_
      rw [Polynomial.natDegree_X_sub_C]
      omega
  -- every agreement point is a root of `R`
  set A : Finset (Fin n) := Finset.univ.filter (fun x : Fin n =>
      (v - P.eval (pts x)) * (z - pts x)⁻¹ = q.eval (pts x)) with hA
  have hroot : ∀ x ∈ A, R.eval (pts x) = 0 := by
    intro x hx
    obtain ⟨-, hx2⟩ := Finset.mem_filter.mp (hA ▸ hx)
    have hzx : z - pts x ≠ 0 := sub_ne_zero_of_ne (Ne.symm (hz x))
    rw [← div_eq_mul_inv, div_eq_iff hzx] at hx2
    simp only [hR, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]
    linear_combination hx2
  have hsub : (A.image pts).val ⊆ R.roots := by
    refine Multiset.subset_iff.mpr ?_
    intro w hw
    obtain ⟨x, hxA, rfl⟩ := Finset.mem_image.mp (by simpa using hw)
    exact Polynomial.mem_roots'.mpr ⟨hR0, hroot x hxA⟩
  have hcard := Polynomial.card_le_degree_of_subset_roots hsub
  rw [Finset.card_image_of_injective _ hinj] at hcard
  exact le_trans hcard hdeg

/-- **⚑ THE PER-COLUMN DEEP-QUOTIENT CONSISTENCY STEP.** If the column's DEEP-quotient word (formed
with the CLAIMED value `v`) is `e`-close to the degree-`< D` code and the radius leaves room
(`e + m < n`, with `m` bounding both `natDegree P` and `D`), then the claimed value is the TRUE
one: `v = P.eval z`. Contrapositive of `deepQuotWord_agree_card_le`: a wrong value caps agreement
at `m`, but `e`-closeness forces agreement `≥ n − e > m`. -/
theorem oodValue_correct_of_close {n D e m : ℕ} {pts : Fin n → K}
    (hinj : Function.Injective pts) {z v : K} (hz : ∀ x, pts x ≠ z)
    {P : Polynomial K} (hP : P.natDegree ≤ m) (hD : 0 < D) (hDm : D ≤ m)
    (hclose : closeN (rsCode pts D) e (fun x => (v - P.eval (pts x)) * (z - pts x)⁻¹))
    (hrad : e + m < n) : v = P.eval z := by
  classical
  by_contra hv
  obtain ⟨g, hg, hcard⟩ := hclose
  obtain ⟨q, hqd, rfl⟩ := (mem_rsCode_iff_lowDegree_evalVec hD).mp hg
  set w : Fin n → K := fun x => (v - P.eval (pts x)) * (z - pts x)⁻¹ with hw
  -- the agreement set and the disagreement set partition the domain
  have hpart := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (p := fun x => w x = evalVec pts q x)
  have hdis : (disagree w (evalVec pts q)).card
      = (Finset.univ.filter (fun x => ¬ (w x = evalVec pts q x))).card := rfl
  have hagree : (Finset.univ.filter (fun x : Fin n =>
      (v - P.eval (pts x)) * (z - pts x)⁻¹ = q.eval (pts x))).card ≤ m :=
    deepQuotWord_agree_card_le hinj hz hP (by omega) hv
  have hagree' : (Finset.univ.filter (fun x => w x = evalVec pts q x)).card ≤ m := hagree
  rw [Finset.card_univ, Fintype.card_fin] at hpart
  rw [← hdis] at hpart
  omega

end Far

/-! ## §5 — The CONVERSE direction: `RlcDistributes`, the correlated-agreement consumption point.

§3 goes columns → batch (a union bound, proved). The DEEP argument needs batch → columns: from
"the ONE reduced word the deployed verifier folds is close to the code" back to "every column's
DEEP-quotient word is close". That is FALSE for a single adversarially-chosen `α` and TRUE, by
BCIKS20 correlated agreement, when many `α` are good. It is stated here as a hypothesis in exactly
the shape of the in-tree affine-line primitive `FriCorrelatedAgreementSharp.CorrelatedAgreementLineAt`
(`FriCorrelatedAgreementSharp.lean:106`) — a `Good : Finset` of challenges, a list-size threshold
`L`, and a COMMON agreement floor — generalized from the 2-term affine line to the `numCols`-term
power-RLC family the deployed reduction actually forms.

**NOT PROVED HERE. NOT AXIOMATIZED.** It occurs only as an explicit hypothesis. -/

section Distribute

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [DecidableEq E] [DecidableEq F]
variable {n c : ℕ}

/-- **`RlcDistributes` — THE CORRELATED-AGREEMENT CONSUMPTION POINT.** If more than `L` challenges
`α` make the power-RLC `Σ_j α^j · u_j` `d`-close to `code`, then there is a SINGLE family of
codewords `g_j ∈ code` and a COMMON set of `≥ agree` domain points on which every `u_j` agrees
with its `g_j` simultaneously.

This is BCIKS20 correlated agreement for the power-RLC family; `agree = |ι| − d` is the
δ-preserving (sharp) instance, `agree = |ι| − 2·d` the two-point one — the same parameterization
`CorrelatedAgreementLineAt` uses. -/
def RlcDistributes (code : Submodule E (Fin n → E)) (d L agree : ℕ)
    (u : Fin c → (Fin n → E)) : Prop :=
  ∀ Good : Finset E,
    (∀ α ∈ Good, closeN code d (fun x => ∑ j : Fin c, α ^ (j : ℕ) * u j x)) →
    L < Good.card →
    ∃ g : Fin c → (Fin n → E), (∀ j, g j ∈ code) ∧
      agree ≤ (Finset.univ.filter (fun x : Fin n => ∀ j, u j x = g j x)).card

/-- The deployed input word IS the power-RLC of the per-column quotient words — so `RlcDistributes`
applies to exactly the family the deployed verifier reduces. -/
theorem friInputWord_eq_rlc (pts : Fin n → F) (α z : E) (M : MatrixOracle (Fin n) c F)
    (vz : Fin c → E) :
    friInputWord pts α z M vz
      = fun x => ∑ j : Fin c, α ^ (j : ℕ) * colQuotWord pts z M vz j x := rfl

/-- **What `RlcDistributes` immediately gives**: a common agreement set of `≥ agree` points makes
EVERY member word `(n − agree)`-close to the code. (The batch → column distribution step, once
CA is available.) -/
theorem closeN_of_rlcDistributes {code : Submodule E (Fin n → E)} {d L agree : ℕ}
    {u : Fin c → (Fin n → E)} (hCA : RlcDistributes code d L agree u)
    (Good : Finset E)
    (hgood : ∀ α ∈ Good, closeN code d (fun x => ∑ j : Fin c, α ^ (j : ℕ) * u j x))
    (hL : L < Good.card) (j : Fin c) :
    closeN code (n - agree) (u j) := by
  classical
  obtain ⟨g, hg, hagree⟩ := hCA Good hgood hL
  refine ⟨g j, hg j, ?_⟩
  have hsub : disagree (u j) (g j)
      ⊆ Finset.univ.filter (fun x : Fin n => ¬ ∀ i, u i x = g i x) := by
    intro x hx
    rw [mem_disagree] at hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun hall => hx (hall j)⟩
  have hpart := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (p := fun x => ∀ i, u i x = g i x)
  rw [Finset.card_univ, Fintype.card_fin] at hpart
  have := Finset.card_le_card hsub
  omega

/-- **NON-VACUITY OF THE `RlcDistributes` SHAPE**: at ONE column it is a THEOREM — the RLC IS the
column, so `d`-closeness at any single good challenge already gives common agreement on `≥ n − d`
points, with `L = 0`. So the `∃ g, agree ≤ …` shape is inhabited and provable; what BCIKS20
correlated agreement supplies is the MULTI-column strengthening at a nontrivial list size `L`.
(Same posture as `FriCorrelatedAgreementSharp.correlatedAgreementLine_twoPoint` for the
affine-line primitive.) -/
theorem rlcDistributes_one_column (code : Submodule E (Fin n → E)) (d : ℕ)
    (u : Fin 1 → (Fin n → E)) : RlcDistributes code d 0 (n - d) u := by
  classical
  intro Good hgood hL
  obtain ⟨α, hα⟩ := Finset.card_pos.mp hL
  have hrlc : (fun x => ∑ j : Fin 1, α ^ (j : ℕ) * u j x) = u 0 := by
    funext x; simp
  obtain ⟨g, hgC, hgcard⟩ := hrlc ▸ hgood α hα
  refine ⟨fun _ => g, fun _ => hgC, ?_⟩
  have hset : (Finset.univ.filter (fun x : Fin n => ∀ j : Fin 1, u j x = g x))
      = Finset.univ.filter (fun x : Fin n => u 0 x = g x) := by
    refine Finset.filter_congr (fun x _ => ?_)
    exact ⟨fun h => h 0, fun h j => by rw [Subsingleton.elim j 0]; exact h⟩
  rw [hset]
  have hpart := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (p := fun x => u 0 x = g x)
  rw [Finset.card_univ, Fintype.card_fin] at hpart
  have hdis : (disagree (u 0) g).card
      = (Finset.univ.filter (fun x => ¬ (u 0 x = g x))).card := rfl
  omega

/-- **⚑ WHAT CORRELATED AGREEMENT BUYS — the DEEP-quotient consistency conclusion, conditional on
`RlcDistributes` and NOTHING else.** For an accepting batch whose committed columns are each
`d`-close to a degree-`≤ m` codeword, if the deployed reduced word is `e`-close to the code for
more than `L` challenges, then EVERY claimed OOD value is the TRUE value of the decoded column at
the out-of-domain point.

This is exactly sub-piece 2's conclusion (`FriDecodedTraceWitness.lean:38-44`), reduced to the one
named primitive. The radius side-condition `(n − agree + d) + m < n` is the honest arithmetic: the
CA agreement floor must beat the code's own degree budget plus the commitment's own error. -/
theorem oodValues_correct_of_rlcDistributes {D d e m agree L : ℕ}
    {pts : Fin n → F} (hinj : Function.Injective pts)
    {z : E} (hz : ∀ x, algebraMap F E (pts x) ≠ z)
    {M : MatrixOracle (Fin n) c F} {vz : Fin c → E} {p : Fin c → Polynomial F}
    (hcols : ∀ j, (disagree (M.col j) (evalVec pts (p j))).card ≤ d)
    (hdeg : ∀ j, (p j).natDegree ≤ m) (hD : 0 < D) (hDm : D ≤ m)
    (hCA : RlcDistributes (rsCode (fun x => algebraMap F E (pts x)) D) e L agree
      (colQuotWord pts z M vz))
    (Good : Finset E)
    (hgood : ∀ α ∈ Good, closeN (rsCode (fun x => algebraMap F E (pts x)) D) e
      (friInputWord pts α z M vz))
    (hL : L < Good.card)
    (hrad : (n - agree + d) + m < n) :
    ∀ j, vz j = ((p j).map (algebraMap F E)).eval z := by
  classical
  intro j
  -- (1) CA distributes the batch closeness to the individual committed quotient word.
  have hcol := closeN_of_rlcDistributes hCA Good (fun α hα => hgood α hα) hL j
  -- (2) replace the committed word by the DECODED column's ideal quotient word (≤ `d` more).
  set ptsE : Fin n → E := fun x => algebraMap F E (pts x) with hptsE
  set P : Polynomial E := (p j).map (algebraMap F E) with hP
  set ideal : Fin n → E := fun x => (vz j - P.eval (ptsE x)) * (z - ptsE x)⁻¹ with hideal
  have hswap : disagree (colQuotWord pts z M vz j) ideal
      ⊆ disagree (M.col j) (evalVec pts (p j)) := by
    intro x hx
    rw [mem_disagree] at hx
    by_contra hcon
    refine hx ?_
    have hentry : M.col j x = (p j).eval (pts x) := by
      by_contra h
      exact hcon (mem_disagree.mpr h)
    simp only [hideal, colQuotWord, deepTerm, hP, hptsE]
    rw [show M.row x j = (p j).eval (pts x) from hentry, algebraMap_eval]
  obtain ⟨g, hgC, hgcard⟩ := hcol
  have hclose2 : closeN (rsCode ptsE D) (n - agree + d) ideal := by
    refine ⟨g, hgC, ?_⟩
    have hsub : disagree ideal g
        ⊆ disagree ideal (colQuotWord pts z M vz j) ∪ disagree (colQuotWord pts z M vz j) g := by
      intro x hx
      rw [mem_disagree] at hx
      by_contra hcon
      simp only [Finset.mem_union, mem_disagree, not_or, not_not] at hcon
      exact hx (hcon.1.trans hcon.2)
    have h1 : (disagree ideal (colQuotWord pts z M vz j)).card ≤ d := by
      have hsymm : disagree ideal (colQuotWord pts z M vz j)
          = disagree (colQuotWord pts z M vz j) ideal := by
        ext x; simp [mem_disagree, ne_comm]
      rw [hsymm]
      exact le_trans (Finset.card_le_card hswap) (hcols j)
    exact le_trans (Finset.card_le_card hsub)
      (le_trans (Finset.card_union_le _ _) (by omega))
  -- (3) the per-column DEEP soundness fact turns closeness into "the claimed value is true".
  have hinjE : Function.Injective ptsE :=
    Function.Injective.comp (algebraMap F E).injective hinj
  have hzE : ∀ x, ptsE x ≠ z := hz
  have hPdeg : P.natDegree ≤ m := le_trans (Polynomial.natDegree_map_le) (hdeg j)
  exact oodValue_correct_of_close hinjE hzE hPdeg hD hDm hclose2 hrad

end Distribute

/-! ## §6 — FIRING on a real instance (`ZMod 17`, 4-point domain, out-of-domain `z = 3`).

The domain is the 4th roots of unity `{1, 4, 16, 13}` (`4` has order `4` mod `17`), `z = 3` is
genuinely OUT of it, and the two committed columns are the evaluations of `X² + 2X + 3` and
`X + 1` (degrees `2, 1 < k = 3`). Everything below is computed, not asserted: the quotient is
pinned as a GENUINE polynomial, its evaluation equals the deployed `(p(z) − p(x))·(z − x)⁻¹`
numerically, the α-RLC and the deployed imperative loop agree, the §2 codeword-membership theorem
fires, and the §4 far bound BITES on a wrong opened value. -/

section Fire

private instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- The firing evaluation domain: the 4th roots of unity in `ZMod 17`. -/
def firePts : Fin 4 → ZMod 17 := ![1, 4, 16, 13]

/-- Committed column `0`'s interpolant (`natDegree 2 < 3`). -/
noncomputable def fireP0 : Polynomial (ZMod 17) := Polynomial.X ^ 2 + 2 * Polynomial.X + 3

/-- Committed column `1`'s interpolant (`natDegree 1 < 3`). -/
noncomputable def fireP1 : Polynomial (ZMod 17) := Polynomial.X + 1

/-- The two committed columns' interpolants. -/
noncomputable def fireP : Fin 2 → Polynomial (ZMod 17) := ![fireP0, fireP1]

/-- The committed 4×2 matrix: row `x` = `(p₀(x), p₁(x))` at the four domain points. -/
def fireM : MatrixOracle (Fin 4) 2 (ZMod 17) := ![![6, 2], ![10, 5], ![2, 0], ![11, 14]]

/-- The (honest) claimed OOD values at `z = 3`: `p₀(3) = 1`, `p₁(3) = 4`. -/
def fireVz : Fin 2 → ZMod 17 := ![1, 4]

theorem fire_z_outside : ∀ x, firePts x ≠ (3 : ZMod 17) := by decide

theorem firePts_inj : Function.Injective firePts := by decide

theorem fireP0_eval_z : fireP0.eval (3 : ZMod 17) = 1 := by
  simp only [fireP0, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_ofNat]
  decide

theorem fireP1_eval_z : fireP1.eval (3 : ZMod 17) = 4 := by
  simp only [fireP1, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  decide

/-- **THE QUOTIENT IS A GENUINE POLYNOMIAL**: `(p₀(X) − p₀(3))/(X − 3) = X + 5`, pinned by
`deepQuot_eq_of_spec` — not a formal fraction, an actual degree-`1` polynomial. -/
theorem fire_deepQuot0 : deepQuot fireP0 (3 : ZMod 17) = Polynomial.X + 5 := by
  refine deepQuot_eq_of_spec ?_
  rw [fireP0_eval_z, show (1 : ZMod 17) = 18 by decide]
  simp only [fireP0, map_ofNat]
  ring

/-- The second column's quotient: `(p₁(X) − p₁(3))/(X − 3) = 1`. -/
theorem fire_deepQuot1 : deepQuot fireP1 (3 : ZMod 17) = 1 := by
  refine deepQuot_eq_of_spec ?_
  rw [fireP1_eval_z]
  simp only [fireP1, map_ofNat]
  ring

/-- **THE EVALUATION MATCHES THE DEPLOYED DIVISION, NUMERICALLY**: at the domain point
`x = firePts 1 = 4`, the quotient polynomial evaluates to `9`, and the deployed
`(p_at_z − p_at_x) * (z − x).inverse()` computes `9` as well. -/
theorem fire_deepQuot_eval_deployed :
    (deepQuot fireP0 (3 : ZMod 17)).eval (firePts 1) = 9 ∧
    (fireP0.eval 3 - fireP0.eval (firePts 1)) * ((3 : ZMod 17) - firePts 1)⁻¹ = 9 := by
  constructor
  · rw [fire_deepQuot0]
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat, firePts]
    decide
  · rw [fireP0_eval_z]
    simp only [fireP0, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_ofNat, firePts]
    decide +kernel

/-- The committed matrix's columns ARE the interpolants' evaluations (the firing is a genuine
codeword commitment, not an arbitrary table). -/
theorem fireM_col : ∀ j, fireM.col j = evalVec firePts (fireP j) := by
  intro j
  funext x
  fin_cases j <;> fin_cases x <;>
    simp [MatrixOracle.col, fireM, fireP, fireP0, fireP1, evalVec, firePts] <;> decide

/-- **THE DEPLOYED IMPERATIVE LOOP FIRES**: folding `(alpha_pow, ro)` from `(1, 0)` over the two
per-column terms `[9, 1]` at `α = 2` returns `alpha_pow = 4 = α²` and `ro = 9 + 2·1 = 11`. -/
theorem fire_reduceOpening : reduceOpening (2 : ZMod 17) [9, 1] = (4, 11) := by decide

/-- **THE INPUT WORD FIRES**, and equals the loop's `ro`: at the sampled row `x = 1` the deployed
reduced opening is `11`. -/
theorem fire_friInputWord : friInputWord firePts (2 : ZMod 17) 3 fireM fireVz 1 = 11 := by
  simp only [friInputWord, colQuotWord, deepTerm, MatrixOracle.row, fireM, fireVz, firePts,
    Algebra.algebraMap_self, RingHom.id_apply, Fin.sum_univ_two]
  decide +kernel

theorem fireP0_natDegree_le : fireP0.natDegree ≤ 2 := by
  unfold fireP0; compute_degree

theorem fireP1_natDegree_le : fireP1.natDegree ≤ 1 := by
  unfold fireP1; compute_degree

theorem fireP_natDegree : ∀ j, (fireP j).natDegree < 3 := by
  intro j
  fin_cases j
  · show fireP0.natDegree < 3
    have := fireP0_natDegree_le; omega
  · show fireP1.natDegree < 3
    have := fireP1_natDegree_le; omega

/-- **§2 FIRES**: the deployed FRI input word of this real commitment IS a codeword of the
degree-`< 2` RS code on the domain — the whole `deepQuot`→`rlcQuotPoly`→membership chain, on a
concrete instance with a real out-of-domain point. -/
theorem fire_friInputWord_mem_rsCode (α : ZMod 17) :
    friInputWord firePts α 3 fireM fireVz
      ∈ rsCode (fun x => algebraMap (ZMod 17) (ZMod 17) (firePts x)) 2 := by
  have h := friInputWord_mem_rsCode (E := ZMod 17) (k := 3) firePts α 3 fireM fireVz fireP
    (fun x => by simpa using fire_z_outside x) fireM_col ?_ fireP_natDegree (by norm_num)
  · simpa using h
  · intro j
    fin_cases j
    · simpa [fireP, fireVz] using fireP0_eval_z.symm
    · simpa [fireP, fireVz] using fireP1_eval_z.symm

/-- **⚑ TEETH — §4 BITES**: with the claimed OOD value `0` instead of the true `p₀(3) = 1`, the
column's DEEP-quotient word is not even `1`-close to the degree-`< 2` code. A wrong opened value
is genuinely detected, at a real radius, on a real instance. -/
theorem fire_wrong_ood_not_close :
    ¬ closeN (rsCode firePts 2) 1
        (fun x => ((0 : ZMod 17) - fireP0.eval (firePts x)) * ((3 : ZMod 17) - firePts x)⁻¹) := by
  intro h
  have hbad := oodValue_correct_of_close (n := 4) (D := 2) (e := 1) (m := 2)
    firePts_inj fire_z_outside fireP0_natDegree_le (by norm_num) (by norm_num) h (by norm_num)
  rw [fireP0_eval_z] at hbad
  exact absurd hbad (by decide)

/-! ### The §5 keystone is NOT vacuously true — its whole hypothesis bundle is inhabited.

A one-column cut of the same fixture: the committed column, its interpolant, and the honest OOD
value. `rlcDistributes_one_column` discharges the CA hypothesis at `numCols = 1`, the radii satisfy
`(n − agree + d) + m < n`, and `oodValues_correct_of_rlcDistributes` then really runs. (At one
column the conclusion is of course also directly available — the point of this firing is
SATISFIABILITY of the hypothesis bundle, i.e. that the keystone is not true-by-emptiness.) -/

/-- The one-column cut of the fixture's commitment. -/
def fireM1 : MatrixOracle (Fin 4) 1 (ZMod 17) := fun x _ => fireM x 0

/-- Its interpolant. -/
noncomputable def fireP1col : Fin 1 → Polynomial (ZMod 17) := fun _ => fireP0

/-- Its honest OOD value at `z = 3`. -/
def fireVz1 : Fin 1 → ZMod 17 := fun _ => 1

theorem fireM1_col : ∀ j, fireM1.col j = evalVec firePts (fireP1col j) := by
  intro j
  have h := fireM_col 0
  funext x
  exact congrFun h x

/-- **NON-VACUITY OF THE §5 KEYSTONE**: the FULL hypothesis bundle of
`oodValues_correct_of_rlcDistributes` is satisfiable on a concrete instance (`ZMod 17`, one column,
`Good = {2}`, radii `d = e = 0`, `m = D = 2`, `agree = 4`), and the theorem really fires. -/
theorem fire_oodValues_correct :
    ∀ j, fireVz1 j = ((fireP1col j).map (algebraMap (ZMod 17) (ZMod 17))).eval 3 := by
  refine oodValues_correct_of_rlcDistributes (n := 4) (c := 1) (D := 2) (d := 0) (e := 0)
    (m := 2) (agree := 4) (L := 0) (pts := firePts) (M := fireM1) (vz := fireVz1)
    (p := fireP1col) firePts_inj (fun x => by simpa using fire_z_outside x) ?_ ?_
    (by norm_num) (by norm_num) (rlcDistributes_one_column _ _ _) {2} ?_ (by decide) (by norm_num)
  · intro j
    simp [fireM1_col j, Dregg2.Circuit.FriSoundness.disagree_eq_empty_iff]
  · intro j
    simpa [fireP1col] using fireP0_natDegree_le
  · intro α _
    rw [Dregg2.Circuit.FriSoundness.closeN_zero_iff_mem]
    exact friInputWord_mem_rsCode (E := ZMod 17) (k := 3) firePts α 3 fireM1 fireVz1 fireP1col
      (fun x => by simpa using fire_z_outside x) fireM1_col
      (fun j => by simpa [fireP1col, fireVz1] using fireP0_eval_z.symm)
      (fun j => by simpa [fireP1col] using lt_of_le_of_lt fireP0_natDegree_le (by norm_num))
      (by norm_num)

/-- **⚑ TEETH — the batch→column converse is FALSE at a SINGLE challenge**, which is exactly why
`RlcDistributes` quantifies over a LARGE `Good` set of challenges and why correlated agreement (not
a one-line argument) is what closes the seam. Two words whose α-RLC at `α = 1` is the ZERO codeword
while the first word is not in the code at all: one good challenge distributes to NOTHING. -/
theorem rlc_single_challenge_no_distribution :
    ∃ u : Fin 2 → (Fin 4 → ZMod 17),
      (fun x => ∑ j : Fin 2, (1 : ZMod 17) ^ (j : ℕ) * u j x) ∈ rsCode firePts 1 ∧
      ¬ closeN (rsCode firePts 1) 0 (u 0) := by
  refine ⟨![fun x => firePts x, fun x => -(firePts x)], ?_, ?_⟩
  · have hzero : (fun x => ∑ j : Fin 2, (1 : ZMod 17) ^ (j : ℕ) *
        (![fun x => firePts x, fun x => -(firePts x)] : Fin 2 → (Fin 4 → ZMod 17)) j x) = 0 := by
      funext x
      simp [Fin.sum_univ_two]
    rw [hzero]
    exact Submodule.zero_mem _
  · intro h
    rw [Dregg2.Circuit.FriSoundness.closeN_zero_iff_mem, mem_rsCode] at h
    obtain ⟨cc, hcc⟩ := h
    have h0 := congrFun hcc 0
    have h1 := congrFun hcc 1
    simp [firePts] at h0 h1
    rw [← h1] at h0
    exact absurd h0 (by decide)

end Fire

#assert_all_clean [
  roStep_foldl,
  reduceOpening_eq,
  reduceOpening_ofFn,
  deepQuot_spec,
  deepQuot_eval_spec,
  deepQuot_eval,
  deepQuot_eval_deployed,
  deepQuot_natDegree,
  deepQuot_natDegree_lt,
  deepQuot_eq_of_spec,
  algebraMap_eval,
  rlcQuotPoly_natDegree_lt,
  friInputWord_eq_loop,
  friInputWord_eq_evalVec,
  friInputWord_mem_rsCode,
  disagree_friInputWord_subset,
  friInputWord_disagree_card_le,
  friInputWord_closeN,
  deepQuotWord_agree_card_le,
  oodValue_correct_of_close,
  friInputWord_eq_rlc,
  closeN_of_rlcDistributes,
  rlcDistributes_one_column,
  oodValues_correct_of_rlcDistributes,
  fire_z_outside,
  firePts_inj,
  fireP0_eval_z,
  fireP1_eval_z,
  fire_deepQuot0,
  fire_deepQuot1,
  fire_deepQuot_eval_deployed,
  fireM_col,
  fire_reduceOpening,
  fire_friInputWord,
  fireP0_natDegree_le,
  fireP1_natDegree_le,
  fireP_natDegree,
  fire_friInputWord_mem_rsCode,
  fireM1_col,
  fire_oodValues_correct,
  fire_wrong_ood_not_close,
  rlc_single_challenge_no_distribution
]

end Dregg2.Circuit.FriDeepQuotientRlc

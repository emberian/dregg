/-
# `Dregg2.Crypto.MlKemRing` — the REAL ML-KEM-768 polynomial ring `R_q = ℤ_q[X]/(X²⁵⁶+1)`, as EXECUTABLE `def`s.

FIPS 203 (ML-KEM). `q = 3329`, `n = 256`. This module builds the negacyclic ring arithmetic and the **Kyber
INCOMPLETE** number-theoretic transform as plain computable `def`s (the same `leanc`-extractable shape as
`Dregg2.Crypto.Keccak` and `Dregg2.Crypto.MlDsaRing`): no `Prop`, no classical choice, only `Nat`/`Array`
arithmetic reduced mod `q` with canonical reps in `[0, q)`.

It is BRICK K1 of replacing the `A = 1`, `n = 1` scalar caricature in `Fips203Kem.lean` (`encapsCore
(A t m : ℤ)`, flagged by the audit as the SAME toy shape we just retired for ML-DSA) with the real
ML-KEM-768 encaps/decaps. Every ML-KEM object — `SampleNTT`/`ExpandA`, the CBD noise, the `A·s`/`t·r`
matrix–vector products — lives in this ring, and the fast path multiplies in the NTT domain.

## ML-KEM's NTT is DIFFERENT from ML-DSA's — the classic Kyber-vs-Dilithium split

ML-DSA (`q = 8380417`) has a primitive **512th** root of unity, so its NTT fully diagonalises
`ℤ_q[X]/(X²⁵⁶+1)` into 256 degree-0 slots and pointwise mult is coefficient product.

ML-KEM (`q = 3329`) does NOT: `ζ = 17` is only a primitive **256th** root (`ζ¹²⁸ = −1`, `ζ²⁵⁶ = 1`), because
`X²⁵⁶+1 ≡ Π_{i<128} (X² − ζ^{2·brv(i)+1}) (mod q)` factors into 128 **quadratics**, not 256 linears. So the
Kyber NTT (`ntt`, 7 layers — not 8) maps a poly to 128 degree-1 polynomials, one per `ℤ_q[X]/(X² − ζ^{2·brv(i)+1})`,
and pointwise mult is the `BaseCaseMultiply` (Alg 12): `(a₀+a₁X)(b₀+b₁X) mod (X²−γ) = (a₀b₀+a₁b₁γ) + (a₀b₁+a₁b₀)X`.
Getting `pointwiseNtt` wrong — plain coefficient product, or the wrong `γ` modulus — is exactly the Kyber pitfall.

## THE ANTI-FAKE GATE (checked, not asserted)

Executable theorems over CONCRETE polynomials pin the transform:

* `zeta_order` — `ζ¹²⁸ ≡ −1` and `ζ²⁵⁶ ≡ 1 (mod q)`: `ζ = 17` is a primitive 256th root (NOT 512th). If it
  were the wrong order the incomplete factorisation would not hold. Kernel `decide` via `powModQ_eq_fold`
  (the `forIn → List.foldl` conversion) — NO compiled-evaluation residual.
* `ntt_intt_id` — `intt (ntt c) = c` FOR ALL canonical reduced polys (round-trip; the inverse, with its
  `128⁻¹ = 3303` scale, is a true inverse). Proven in `Dregg2.Crypto.MlKemNttFaithful` (which characterizes
  THIS module's imperative loops entrywise) — a ∀-theorem, axiom-clean, no `native_decide`.
* `ntt_computes_negacyclic_mul` — `intt (pointwiseNtt (ntt a) (ntt b)) = schoolbookMul a b` FOR ALL size-256
  poly pairs. THE load-bearing gate: it forces the incomplete NTT + the `BaseCaseMultiply` base-case moduli
  `γ_i = ζ^{2·brv(i)+1}` to ALL be right — a plain coefficient product would fail it. Also a ∀-theorem in
  `MlKemNttFaithful` (= `mlkem_ntt_ring_faithful` under its gate name), axiom-clean, no `native_decide`.
  (Both were formerly one-sample `native_decide` gates here; the samples survive there as kernel-clean
  specializations.)

No `sorry`, no user `axiom`, no toy substitute for the transform.

## RESIDUAL

None from this module: NO `native_decide` remains here (the former compiled-evaluation residual on the two
poly-loop gates is GONE — they are ∀-proven in `MlKemNttFaithful`). `zeta_order` is kernel-`decide`-clean:
axiom set ⊆ {propext, Classical.choice, Quot.sound}.
-/

namespace Dregg2.Crypto.MlKemRing

/-! ## `ℤ_q` scalar arithmetic (`q = 3329`, canonical reps in `[0, q)`) -/

/-- The ML-KEM modulus, FIPS 203 §2.3: `q = 3329 = 13·256 + 1` (so `256 | q − 1`, giving a 256th root). -/
def q : Nat := 3329

/-- Modular add of two canonical reps in `[0, q)`. -/
@[inline] def addQ (a b : Nat) : Nat := (a + b) % q

/-- Modular subtract of two canonical reps in `[0, q)` (`a − b mod q`, kept nonnegative). -/
@[inline] def subQ (a b : Nat) : Nat := (a + q - b) % q

/-- Modular multiply, reducing the full product mod `q`. -/
@[inline] def mulModQ (a b : Nat) : Nat := (a * b) % q

/-- Modular exponentiation by square-and-multiply. Exponents used here are `< 512` (`2·brv(i)+1 ≤ 255`, plus
the `256` order check), so a fixed 32-bit ladder covers them (spent-exponent squarings are harmless no-ops). -/
def powModQ (base e : Nat) : Nat := Id.run do
  let mut result := 1
  let mut b := base % q
  let mut ex := e
  for _ in [0:32] do
    if ex % 2 == 1 then result := mulModQ result b
    b := mulModQ b b
    ex := ex / 2
  return result

/-- The desugared square-and-multiply step of `powModQ`; state `(b, ex, result)`. -/
def pstep (st : Nat × Nat × Nat) (_ : Nat) : Nat × Nat × Nat :=
  (mulModQ st.1 st.1, st.2.1 / 2, if st.2.1 % 2 == 1 then mulModQ st.2.2 st.1 else st.2.2)

/-- The `forIn` body of `powModQ`, as a fold over the state `(result, b, ex)`, is `pstep` on the rotated
state `(b, ex, result)`. -/
private theorem foldl_body_eq_pstep (l : List Nat) (r b ex : Nat) :
    List.foldl (fun (s : Nat × Nat × Nat) (_ : Nat) =>
        if (s.2.2 % 2 == 1) = true then (mulModQ s.1 s.2.1, mulModQ s.2.1 s.2.1, s.2.2 / 2)
        else (s.1, mulModQ s.2.1 s.2.1, s.2.2 / 2)) (r, b, ex) l =
      ((List.foldl pstep (b, ex, r) l).2.2, (List.foldl pstep (b, ex, r) l).1,
        (List.foldl pstep (b, ex, r) l).2.1) := by
  induction l generalizing r b ex with
  | nil => rfl
  | cons a l ih =>
    by_cases h : (ex % 2 == 1) = true
    · simp only [List.foldl_cons, h, if_true, ih, pstep]
    · simp only [List.foldl_cons, h, Bool.false_eq_true, if_false, ih, pstep]

/-- **`powModQ` as the explicit 32-step ladder fold** (`result` is the third component). The `for _ in
[0:32]` loop desugars to `Std.Range.forIn`, whose well-founded recursion the KERNEL cannot reduce — so
concrete `powModQ` facts get stuck under `decide`. `List.foldl` over the concrete `List.range' 0 32 1`
DOES kernel-reduce; rewriting through this lemma is what lets `zeta_order` close by kernel `decide`
(no `Lean.ofReduceBool`/`trustCompiler`). Consumed upstream by `MlKemNttFaithful`'s ladder invariant. -/
theorem powModQ_eq_fold (base e : Nat) :
    powModQ base e = (List.foldl pstep (base % q, e, 1) (List.range' 0 32 1)).2.2 := by
  unfold powModQ
  -- `← apply_ite` loops on v4.35; push the `if` through `pure (ForInStep.yield ·)` with this
  -- one instance instead.
  have hite : ∀ (c : Prop) [Decidable c] (a b : Nat × Nat × Nat),
      (if c then (pure (ForInStep.yield a) : Id (ForInStep (Nat × Nat × Nat)))
        else pure (ForInStep.yield b)) = pure (ForInStep.yield (if c then a else b)) :=
    fun c _ a b => (apply_ite (fun x => (pure (ForInStep.yield x) : Id _)) c a b).symm
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    hite, List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  exact congrArg Prod.fst (foldl_body_eq_pstep (List.range' 0 32) 1 (base % q) e)

/-! ## The negacyclic ring `R_q = ℤ_q[X]/(X²⁵⁶+1)` -/

/-- A polynomial in `R_q`: 256 coefficients, each a canonical `ℤ_q` rep in `[0, q)`, coefficient `i` = the
`Xⁱ` term. -/
abbrev Poly := Array Nat

/-- The zero polynomial. -/
def zeroPoly : Poly := Array.replicate 256 0

/-- Set coefficient `i` to `v` (reduced mod `q`). Convenience for building concrete test polynomials. -/
def setC (p : Poly) (i v : Nat) : Poly := p.set! i (v % q)

/-- Coefficient-wise sum in `R_q`. -/
def addPoly (a b : Poly) : Poly := Id.run do
  let mut c := zeroPoly
  for i in [0:256] do
    c := c.set! i (addQ a[i]! b[i]!)
  return c

/-- Coefficient-wise difference in `R_q`. -/
def subPoly (a b : Poly) : Poly := Id.run do
  let mut c := zeroPoly
  for i in [0:256] do
    c := c.set! i (subQ a[i]! b[i]!)
  return c

/-- **The ground-truth negacyclic product** `(a·b) mod (X²⁵⁶+1)` in `R_q`. Schoolbook convolution with the
`X²⁵⁶ = −1` wrap: `c_k = Σ_{i+j=k} a_i b_j − Σ_{i+j=k+256} a_i b_j`, all mod `q`. This is the reference the
fast NTT path is checked against. -/
def schoolbookMul (a b : Poly) : Poly := Id.run do
  let mut c := zeroPoly
  for i in [0:256] do
    for j in [0:256] do
      let prod := mulModQ a[i]! b[j]!
      let k := i + j
      if k < 256 then
        c := c.set! k (addQ c[k]! prod)                 -- Xⁱ⁺ʲ, no wrap
      else
        c := c.set! (k - 256) (subQ c[k - 256]! prod)   -- X²⁵⁶ = −1 : subtract
  return c

/-! ## The ML-KEM (Kyber) INCOMPLETE number-theoretic transform (FIPS 203 §4.3, Algorithms 9, 10, 11, 12)

`q = 3329` admits a primitive **256th** root of unity `ζ = 17` (`ζ¹²⁸ ≡ −1`, `ζ²⁵⁶ ≡ 1`). The forward NTT
(Algorithm 9) is a length-256 Cooley–Tukey transform of **7** stages (`len = 128 … 2`, NOT down to 1), whose
twiddle at counter `i` is `ζ^{brv(i)}` with `brv` reversing the low **7** bits of `i`. It leaves the poly as
128 degree-1 residues, one per `ℤ_q[X]/(X² − ζ^{2·brv(i)+1})`. The inverse (Algorithm 10) is the
Gentleman–Sande dual with twiddle `ζ^{brv(i)}` (`i` counting down `127 … 1`) followed by scaling every
coefficient by `128⁻¹ mod q = 3303`. Pointwise mult (`MultiplyNTTs`, Algorithm 11) is 128 `BaseCaseMultiply`
(Algorithm 12) products in those quadratic quotients. -/

/-- ML-KEM's primitive 256th root of unity mod `q`, FIPS 203. -/
def zeta : Nat := 17

/-- `128⁻¹ mod q`, FIPS 203 (the `intt` final scaling — `128·3303 = 422784 = 127·3329 + 1`). -/
def nInv : Nat := 3303

/-- Reverse the low **7** bits of `k` (FIPS 203's `BitRev7`). NB: 7 bits, because the Kyber NTT counter runs
`1 … 127` (7 layers), not `1 … 255` — this is the incomplete-NTT signature. -/
def brv7 (k : Nat) : Nat := Id.run do
  let mut r := 0
  let mut x := k
  for _ in [0:7] do
    r := r * 2 + x % 2
    x := x / 2
  return r

/-- The FIPS 203 twiddle at counter `i`: `ζ^{brv(i)} mod q`. -/
def zetaTwiddle (i : Nat) : Nat := powModQ zeta (brv7 i)

/-- **Forward NTT** (FIPS 203 Algorithm 9). Seven Cooley–Tukey stages, `len = 128, 64, …, 2` (stops at 2, NOT
1 — the transform is INCOMPLETE), twiddle counter `i = 1 … 127`. -/
def ntt (w : Poly) : Poly := Id.run do
  let mut a := w
  let mut i := 1
  for s in [0:7] do
    let len := 128 >>> s                 -- 128, 64, …, 2  (7 stages)
    let nblk := 128 / len                -- 256 / (2·len) = number of blocks this stage
    for blk in [0:nblk] do
      let start := blk * 2 * len
      let z := zetaTwiddle i
      i := i + 1
      for j in [start : start + len] do
        let t := mulModQ z a[j + len]!
        a := a.set! (j + len) (subQ a[j]! t)
        a := a.set! j (addQ a[j]! t)
  return a

/-- **Inverse NTT** (FIPS 203 Algorithm 10). Gentleman–Sande dual: seven stages `len = 2, 4, …, 128`, twiddle
`ζ^{brv(i)}` with `i` counting down `127 … 1`, then scale every coefficient by `128⁻¹ mod q = 3303`. -/
def intt (w : Poly) : Poly := Id.run do
  let mut a := w
  let mut i := 127
  for s in [0:7] do
    let len := 2 <<< s                   -- 2, 4, …, 128  (7 stages)
    let nblk := 128 / len                -- number of blocks this stage
    for blk in [0:nblk] do
      let start := blk * 2 * len
      let z := zetaTwiddle i
      i := i - 1
      for j in [start : start + len] do
        let t := a[j]!
        a := a.set! j (addQ t a[j + len]!)
        a := a.set! (j + len) (mulModQ z (subQ a[j + len]! t))
  for j in [0:256] do
    a := a.set! j (mulModQ nInv a[j]!)    -- scale by 128⁻¹ mod q
  return a

/-- **BaseCaseMultiply** (FIPS 203 Algorithm 12): the product of two degree-1 polys `a₀+a₁X`, `b₀+b₁X` in the
quadratic quotient `ℤ_q[X]/(X² − γ)`: `c₀ = a₀b₀ + a₁b₁γ`, `c₁ = a₀b₁ + a₁b₀` (using `X² = γ`). -/
def baseCaseMultiply (a0 a1 b0 b1 gamma : Nat) : Nat × Nat :=
  ( addQ (mulModQ a0 b0) (mulModQ (mulModQ a1 b1) gamma)
  , addQ (mulModQ a0 b1) (mulModQ a1 b0) )

/-- **Pointwise mult in the NTT domain** (FIPS 203 Algorithm 11, `MultiplyNTTs`). NOT a coefficient product:
for each of the 128 degree-1 slots `i`, `BaseCaseMultiply` over `ℤ_q[X]/(X² − ζ^{2·brv(i)+1})`. -/
def pointwiseNtt (a b : Poly) : Poly := Id.run do
  let mut c := zeroPoly
  for i in [0:128] do
    let gamma := powModQ zeta (2 * brv7 i + 1)
    let (c0, c1) := baseCaseMultiply a[2*i]! a[2*i+1]! b[2*i]! b[2*i+1]! gamma
    c := c.set! (2*i) c0
    c := c.set! (2*i+1) c1
  return c

/-! ## THE ANTI-FAKE GATE — executable theorems (kernel `decide` for the ζ order; the poly-loop gates
`ntt_intt_id` / `ntt_computes_negacyclic_mul` are ∀-theorems in `Dregg2.Crypto.MlKemNttFaithful`, proven
from these very loop defs, axiom-clean — no `native_decide` anywhere in this module).

If the ζ order, the 7-bit reversal, the `intt` scaling, or the base-case moduli were wrong, these fail. -/

/-- A concrete nonzero test poly with a high-degree term: `a = 1 + 2·X + 7·X²⁵⁵`. -/
def sampleA : Poly := setC (setC (setC zeroPoly 0 1) 1 2) 255 7

/-- A second concrete test poly with high-degree terms: `b = 4 + 5·X¹⁰⁰ + 6·X²⁰⁰`. -/
def sampleB : Poly := setC (setC (setC zeroPoly 0 4) 100 5) 200 6

/-- **`ζ = 17` is a primitive 256th root** (NOT 512th): `ζ¹²⁸ ≡ −1` and `ζ²⁵⁶ ≡ 1 (mod q)`. The property that
makes the INCOMPLETE Kyber factorisation `X²⁵⁶+1 = Π(X² − ζ^{2·brv(i)+1})` hold.
Kernel `decide` via `powModQ_eq_fold` (the `forIn → List.foldl` conversion; `Std.Range.forIn`'s
well-founded recursion does not kernel-reduce, the concrete fold does) — NO
`Lean.ofReduceBool`/`trustCompiler` residual. -/
theorem zeta_order : powModQ zeta 128 = q - 1 ∧ powModQ zeta 256 = 1 := by
  rw [powModQ_eq_fold zeta 128, powModQ_eq_fold zeta 256]; decide

end Dregg2.Crypto.MlKemRing

/-
# `Dregg2.Crypto.MlDsaRing` — the REAL ML-DSA-65 polynomial ring `R_q = ℤ_q[X]/(X²⁵⁶+1)`, as EXECUTABLE `def`s.

FIPS 204. `q = 8380417`, `n = 256`. This module builds the negacyclic ring arithmetic and the ML-DSA
number-theoretic transform as plain computable `def`s (the same `leanc`-extractable shape as
`Dregg2.Crypto.Keccak` — BRICK 1, already byte-exact): no `Prop`, no classical choice, only `Nat`/`Array`
arithmetic reduced mod `q` with canonical reps in `[0, q)`.

It is BRICK 2 of replacing the `A = id` scalar caricature in `Fips204Verify.lean` with the real ML-DSA-65
verify. Every ML-DSA object — `SampleInBall`, `ExpandA`, the `t`/`z`/`w` vectors, the `A·z` matrix product —
lives in this ring, and the fast path multiplies polynomials in the NTT domain. So the correctness of the
whole verify rests on THIS module's `ntt`/`intt` being an honest length-256 negacyclic transform: the fast
`intt (pointwiseMul (ntt a) (ntt b))` must equal the ground-truth `schoolbookMul a b` (the real
`(a·b) mod (X²⁵⁶+1)` product, with the `X²⁵⁶ = −1` sign on wraparound).

## THE ANTI-FAKE GATE (checked, not asserted)

Executable theorems pin the transform:

* `ntt_intt_id` — `intt (ntt c) = c` FOR ALL canonical reduced polys (round-trip; the inverse is a true
  inverse). Proven in `Dregg2.Crypto.NttFaithful` (which characterizes THIS module's imperative loop defs
  entrywise and closes the CT/GS stage inductions) — a ∀-theorem, axiom-clean, no `native_decide`. It
  lives there (not here) only because the proof needs Mathlib's `ZMod`; the statement is about these defs.
* `ntt_computes_negacyclic_mul` — `intt (pointwiseMul (ntt a) (ntt b)) = schoolbookMul a b` FOR ALL
  size-256 poly pairs. THE load-bearing gate: the fast transform equals the real negacyclic ring product.
  Also a ∀-theorem in `Dregg2.Crypto.NttFaithful` (= `ringRepFaithful_proven` under its gate name),
  axiom-clean, no `native_decide`. (Both were formerly one-sample `native_decide` gates here; the samples
  survive there as kernel-clean specializations, `nttLeftInverse_sample`/`ntt_negacyclic_mul_sample`.)
* `zeta_primitive_512th_root` — `ζ²⁵⁶ ≡ −1 (mod q)` for `ζ = 1753` (the property that makes the negacyclic
  NTT well-defined at all). Kernel `decide` via `powModQ_eq_fold` (the `forIn → List.foldl` conversion) —
  NO compiled-evaluation residual.
* `mul_mod_q_sanity` — `(q−1)·(q−1) ≡ 1 (mod q)` (reduction sanity). Kernel `decide`.

If the ζ-power order (FIPS 204 Algorithm 41 uses `ζ^{brv(k)}`, the 8-bit-reversed exponent), the
bit-reversal, or the `intt` scaling (`256⁻¹ mod q = 8347681`) were wrong, these theorems would NOT close.
No `sorry`, no user `axiom`, no toy substitute for the transform.

## RESIDUAL

None from this module: NO `native_decide` remains here (the former compiled-evaluation residual on the two
poly-loop gates is GONE — they are ∀-proven in `NttFaithful`). The scalar gates
(`zeta_primitive_512th_root`, `mul_mod_q_sanity`) are kernel-`decide`-clean: axiom set ⊆
{propext, Classical.choice, Quot.sound}.
-/

namespace Dregg2.Crypto.MlDsaRing

/-! ## `ℤ_q` scalar arithmetic (`q = 8380417`, canonical reps in `[0, q)`) -/

/-- The ML-DSA modulus, FIPS 204 Table 1: `q = 2²³ − 2¹³ + 1 = 8380417`. -/
def q : Nat := 8380417

/-- Modular add of two canonical reps in `[0, q)`. -/
@[inline] def addQ (a b : Nat) : Nat := (a + b) % q

/-- Modular subtract of two canonical reps in `[0, q)` (`a − b mod q`, kept nonnegative). -/
@[inline] def subQ (a b : Nat) : Nat := (a + q - b) % q

/-- Modular multiply, reducing the full product mod `q`. -/
@[inline] def mulModQ (a b : Nat) : Nat := (a * b) % q

/-- Modular exponentiation by square-and-multiply. Exponents used here are `< 512`, so a fixed 32-bit ladder
covers them (once the exponent is exhausted the remaining squarings are harmless no-ops on `result`). -/
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
DOES kernel-reduce; rewriting through this lemma is what lets `zeta_primitive_512th_root` close by kernel
`decide` (no `Lean.ofReduceBool`/`trustCompiler`). Consumed upstream by `NttFaithful`'s ladder invariant. -/
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
        c := c.set! k (addQ c[k]! prod)          -- Xⁱ⁺ʲ, no wrap
      else
        c := c.set! (k - 256) (subQ c[k - 256]! prod)   -- X²⁵⁶ = −1 : subtract
  return c

/-! ## The ML-DSA number-theoretic transform (FIPS 204 §7.5, Algorithms 41 & 42)

`q = 8380417` admits a primitive 512th root of unity `ζ = 1753`. The forward NTT (Algorithm 41) is a
length-256 negacyclic Cooley–Tukey transform whose twiddle at step `k` is `ζ^{brv(k)}`, where `brv` reverses
the low 8 bits of `k`. The inverse (Algorithm 42) is the Gentleman–Sande dual with twiddle `−ζ^{brv(k)}`
followed by scaling every coefficient by `256⁻¹ mod q = 8347681`. -/

/-- ML-DSA's primitive 512th root of unity mod `q`, FIPS 204. -/
def zeta : Nat := 1753

/-- `256⁻¹ mod q`, FIPS 204 (the `intt` final scaling). -/
def nInv : Nat := 8347681

/-- Reverse the low 8 bits of `k` (FIPS 204's `brv`). -/
def brv8 (k : Nat) : Nat := Id.run do
  let mut r := 0
  let mut x := k
  for _ in [0:8] do
    r := r * 2 + x % 2
    x := x / 2
  return r

/-- The FIPS 204 twiddle at step `k`: `ζ^{brv(k)} mod q`. -/
def zetaTwiddle (k : Nat) : Nat := powModQ zeta (brv8 k)

/-- **Forward NTT** (FIPS 204 Algorithm 41). Eight Cooley–Tukey stages, `len = 128, 64, …, 1`; at stage `s`
there are `128/len` butterfly blocks, each consuming the next twiddle `k = 1 … 255` in order. -/
def ntt (w : Poly) : Poly := Id.run do
  let mut a := w
  let mut k := 0
  for s in [0:8] do
    let len := 128 >>> s              -- 128, 64, …, 1
    let nblk := 128 / len             -- 256 / (2·len) = number of blocks this stage
    for blk in [0:nblk] do
      let start := blk * 2 * len
      k := k + 1
      let z := zetaTwiddle k
      for j in [start : start + len] do
        let t := mulModQ z a[j + len]!
        a := a.set! (j + len) (subQ a[j]! t)
        a := a.set! j (addQ a[j]! t)
  return a

/-- **Inverse NTT** (FIPS 204 Algorithm 42). Gentleman–Sande dual: eight stages `len = 1, 2, …, 128`, twiddle
`−ζ^{brv(k)}` with `k` counting down `255 … 1`, then scale every coefficient by `256⁻¹ mod q`. -/
def intt (w : Poly) : Poly := Id.run do
  let mut a := w
  let mut k := 256
  for s in [0:8] do
    let len := 1 <<< s                -- 1, 2, …, 128
    let nblk := 128 / len             -- number of blocks this stage
    for blk in [0:nblk] do
      let start := blk * 2 * len
      k := k - 1
      let z := subQ 0 (zetaTwiddle k)  -- −ζ^{brv(k)} mod q
      for j in [start : start + len] do
        let t := a[j]!
        a := a.set! j (addQ t a[j + len]!)
        a := a.set! (j + len) (mulModQ z (subQ t a[j + len]!))
  for j in [0:256] do
    a := a.set! j (mulModQ nInv a[j]!)   -- scale by 256⁻¹ mod q
  return a

/-- Coefficient-wise product in the NTT domain (the fast negacyclic multiply combines with `ntt`/`intt`). -/
def pointwiseMul (a b : Poly) : Poly := Id.run do
  let mut c := zeroPoly
  for i in [0:256] do
    c := c.set! i (mulModQ a[i]! b[i]!)
  return c

/-! ## THE ANTI-FAKE GATE — executable theorems (kernel `decide` for the scalar facts; the poly-loop
gates `ntt_intt_id` / `ntt_computes_negacyclic_mul` are ∀-theorems in `Dregg2.Crypto.NttFaithful`,
proven from these very loop defs, axiom-clean — no `native_decide` anywhere in this module).

If the ζ-power order, the bit-reversal, or the `intt` scaling were wrong, these would NOT close. -/

/-- A concrete nonzero test poly with a high-degree term: `a = 1 + 2·X + 7·X²⁵⁵`. -/
def sampleA : Poly := setC (setC (setC zeroPoly 0 1) 1 2) 255 7

/-- A second concrete test poly with high-degree terms: `b = 4 + 5·X¹⁰⁰ + 6·X²⁰⁰`. -/
def sampleB : Poly := setC (setC (setC zeroPoly 0 4) 100 5) 200 6

/-- **Reduction sanity**: `(q−1)·(q−1) ≡ 1 (mod q)`. Kernel `decide` (no loop; pure `Nat` `*`/`%`),
so this carries NO `Lean.ofReduceBool`/`trustCompiler` — axiom set ⊆ {propext, Classical.choice, Quot.sound}. -/
theorem mul_mod_q_sanity : mulModQ (q - 1) (q - 1) = 1 := by decide

/-- **`ζ` is a primitive 512th root**: `ζ²⁵⁶ ≡ −1 (mod q)`. The property that makes the negacyclic NTT
well-defined; if `ζ = 1753` or `q` were wrong this fails.
Kernel `decide` via `powModQ_eq_fold`: the `for _ in [0:32]` ladder itself does NOT kernel-reduce
(`Std.Range.forIn` is well-founded recursion), but the equivalent `List.foldl` over the concrete
`List.range' 0 32 1` does — so this carries NO `Lean.ofReduceBool`/`trustCompiler` residual. -/
theorem zeta_primitive_512th_root : powModQ zeta 256 = q - 1 := by
  rw [powModQ_eq_fold]; decide

/-! ## FAST RUNTIME TWINS — `@[implemented_by]` over `Array UInt32` coefficients with `UInt64` products.

The pure `def`s above store each coefficient as a boxed `Nat`, so every NTT butterfly / schoolbook step
dispatches through `lean_nat_add`/`lean_nat_mul`/`lean_nat_mod` on heap bignums. These twins keep the coeffs
in an UNBOXED `Array UInt32` and do machine arithmetic in the inner loops, converting to/from `Array Nat`
only at the boundary. Each is attached to its pure def by `@[implemented_by]` so `MlDsaVerifyReal.verifyCore`
and `MlDsaSignReal.signCore` — which call these ops directly — run the fast path with NO change to the
callers and NO change to the proofs (`@[implemented_by]` is runtime-only; the kernel and `NttFaithful`'s
∀-theorems still see the pure `Nat` bodies).

**THE CORRECTNESS CRUX (why a naive `Array UInt32` port is WRONG).** Canonical coeffs are `< q ≈ 2²³`, so a
COEFFICIENT PRODUCT reaches `< 2⁴⁶` — which TRUNCATES in a 32-bit multiply. Every modular multiply therefore
forms the product in `UInt64` and reduces mod `q` before narrowing back to `UInt32` (`mulQu`). Adds/subs stay
in `UInt32`: for canonical inputs `a,b < q`, `a + b < 2q < 2²⁴` and `a + q − b < 2²⁴`, both well under `2³²`,
so no overflow (the pure defs already document the canonical-rep `[0,q)` precondition; all producers reduce).

**TRUSTED — `@[implemented_by]` carries NO proof obligation** (a wrong twin silently corrupts sign/verify).
Two live gates catch it: (1) the `#guard` differentials below pin each twin against the pure ground truth
(`schoolbookMul`, kept pure, and inline `(a·b) mod q` formulas) — a genuine fast-vs-pure comparison, NOT
fast-vs-fast, since the pure `schoolbookMul`/`Nat` arithmetic is not routed; (2) end-to-end, the byte-exact
NIST-ACVP vectors (`AcvpKats`, sign floor) and `MlDsaVerifyReal.verify_accepts_real` (`native_decide`, in the
default build) drive these ops through `signCore`/`verifyCore` and would go RED on any byte deviation. -/

/-- `q` as a `UInt32` (canonical coeff reduction target). -/
@[inline] def qU : UInt32 := 8380417
/-- `q` as a `UInt64` (product-reduction modulus; a coeff product `< 2⁴⁶` fits here, not in `UInt32`). -/
@[inline] def qU64 : UInt64 := 8380417

/-- Modular add of canonical `UInt32` reps `< q`: `a + b < 2q < 2²⁴`, no 32-bit overflow. -/
@[inline] def addQu (a b : UInt32) : UInt32 := (a + b) % qU
/-- Modular sub of canonical `UInt32` reps `< q`: `a + q < 2²⁴` and `> b`, so no underflow/overflow. -/
@[inline] def subQu (a b : UInt32) : UInt32 := (a + qU - b) % qU
/-- Modular mul: the product of two `< q ≈ 2²³` reps reaches `< 2⁴⁶`, so it is formed in `UInt64`
BEFORE reducing mod `q` and narrowing — a bare `UInt32` product would truncate at 32 bits. -/
@[inline] def mulQu (a b : UInt32) : UInt32 := ((a.toUInt64 * b.toUInt64) % qU64).toUInt32

/-- Widen a `Poly` (canonical `Nat` coeffs `< q < 2³²`) to unboxed `UInt32`; faithful since coeffs `< 2³²`. -/
@[inline] def toU32 (p : Poly) : Array UInt32 := p.map Nat.toUInt32
/-- Narrow an `Array UInt32` back to `Poly` (`Nat` coeffs); faithful (`UInt32.toNat` is exact `< 2³²`). -/
@[inline] def toNatA (p : Array UInt32) : Poly := p.map UInt32.toNat

/-- Fast twin of `addPoly`. -/
def fastAddPoly (a b : Poly) : Poly := Id.run do
  let au := toU32 a; let bu := toU32 b
  let mut c : Array UInt32 := Array.replicate 256 0
  for i in [0:256] do
    c := c.set! i (addQu au[i]! bu[i]!)
  return toNatA c

/-- Fast twin of `subPoly`. -/
def fastSubPoly (a b : Poly) : Poly := Id.run do
  let au := toU32 a; let bu := toU32 b
  let mut c : Array UInt32 := Array.replicate 256 0
  for i in [0:256] do
    c := c.set! i (subQu au[i]! bu[i]!)
  return toNatA c

/-- Fast twin of `pointwiseMul` (`UInt64` products). -/
def fastPointwiseMul (a b : Poly) : Poly := Id.run do
  let au := toU32 a; let bu := toU32 b
  let mut c : Array UInt32 := Array.replicate 256 0
  for i in [0:256] do
    c := c.set! i (mulQu au[i]! bu[i]!)
  return toNatA c

/-- Fast twin of `schoolbookMul` (the negacyclic reference; `UInt64` products, `UInt32` accumulator).
NOT attached via `@[implemented_by]` — `schoolbookMul` is never on the sign/verify runtime path (it is
`NttFaithful`'s proof ground truth), so it stays a pure, unrouted reference for the differentials below. -/
def fastSchoolbookMul (a b : Poly) : Poly := Id.run do
  let au := toU32 a; let bu := toU32 b
  let mut c : Array UInt32 := Array.replicate 256 0
  for i in [0:256] do
    for j in [0:256] do
      let prod := mulQu au[i]! bu[j]!
      let k := i + j
      if k < 256 then
        c := c.set! k (addQu c[k]! prod)
      else
        c := c.set! (k - 256) (subQu c[k - 256]! prod)
  return toNatA c

/-- Fast twin of `ntt` (FIPS 204 Algorithm 41), a line-for-line mirror over `Array UInt32` coeffs; the
twiddle `ζ^{brv(k)}` is computed once per block and narrowed to `UInt32`, the butterfly does `UInt64`
products via `mulQu`. -/
def fastNtt (w : Poly) : Poly := Id.run do
  let mut a := toU32 w
  let mut k := 0
  for s in [0:8] do
    let len := 128 >>> s
    let nblk := 128 / len
    for blk in [0:nblk] do
      let start := blk * 2 * len
      k := k + 1
      let z := (zetaTwiddle k).toUInt32
      for j in [start : start + len] do
        let t := mulQu z a[j + len]!
        a := a.set! (j + len) (subQu a[j]! t)
        a := a.set! j (addQu a[j]! t)
  return toNatA a

/-- Fast twin of `intt` (FIPS 204 Algorithm 42), mirroring the Gentleman–Sande dual + the `256⁻¹` scaling. -/
def fastIntt (w : Poly) : Poly := Id.run do
  let mut a := toU32 w
  let mut k := 256
  for s in [0:8] do
    let len := 1 <<< s
    let nblk := 128 / len
    for blk in [0:nblk] do
      let start := blk * 2 * len
      k := k - 1
      let z := (subQ 0 (zetaTwiddle k)).toUInt32   -- −ζ^{brv(k)} mod q, narrowed
      for j in [start : start + len] do
        let t := a[j]!
        a := a.set! j (addQu t a[j + len]!)
        a := a.set! (j + len) (mulQu z (subQu t a[j + len]!))
  let nInvU := nInv.toUInt32
  for j in [0:256] do
    a := a.set! j (mulQu nInvU a[j]!)
  return toNatA a

/-! ### ⚑ THE ROUTED ALIASES — why NO `@[implemented_by]` sits on a pure def here.

`@[implemented_by]` is honoured by the COMPILED evaluator, and `#guard`/`native_decide`/`#eval` all
run on that evaluator. So an attribute attached to the pure def makes **its own differential a
tautology**. Demonstrated (2026-08-09):

    def pureF (n : Nat) : Nat := n + 1
    def twinF (n : Nat) : Nat := n + 999
    attribute [implemented_by twinF] pureF
    #eval pureF 1                    -- 1000  — the TWIN answers
    #eval (twinF 1 == pureF 1)       -- true  — for ANY twin, always
    theorem k : pureF 1 = 2 := rfl   -- and the kernel still sees the pure body

Until today these five attributes were on `addPoly`/`subPoly`/`pointwiseMul`/`ntt`/`intt`
themselves. `fastNtt x == ntt x` was therefore **fast-vs-fast**: not merely untested, but
UNTESTABLE — writing the obvious check would have produced a permanently green tautology, which is
worse than no check because it reads as closure. The only two tests that touched `ntt`/`intt` were
the composite product and the round trip, and a constructed twin pair (`fastNtt` post-composed with
`List.reverse`, `fastIntt` pre-composed with the same involution — pointwise multiplication is
permutation-equivariant) satisfies BOTH while differing from the routed twin, on the live sign and
verify path. That falsifier is rebuilt and evaluated in `Dregg2.Crypto.MlDsaRingTwinDifferential`.

So each attribute now sits on a `…Fast` ALIAS, and the EXECUTABLE callers (`MlDsaVerifyReal`,
`MlDsaSignReal`, `MlDsaKeygen`) call the alias. Consequences, all of them the point:

  * the pure `ntt`/`intt`/`addPoly`/`subPoly`/`pointwiseMul` keep their NORMAL compilation, so
    `fastNtt x == ntt x` is now a genuine fast-vs-pure comparison — a differential that can go RED;
  * the alias is `rfl`-equal to its pure def (`…Fast_eq` below), so every existing theorem,
    including `NttFaithful`'s ∀-theorems, transports unchanged and the kernel sees the same object;
  * `@[implemented_by]` still carries NO proof obligation. What changed is that the obligation is
    now DISCHARGEABLE by evidence instead of unstatable.

This is the structure `Distributed.BlocklaceFinality` already had (`:1373`, attribute on the
`tauOrderFast` alias, pure `tauOrder` left unrouted) — the sixth and only seam in the tree that was
already testable. It is why that seam has a real differential and these five did not. -/

/-- Routed alias of `addPoly` — `rfl`-equal to it; carries the `@[implemented_by]` so the pure def
stays unrouted and comparable. -/
def addPolyFast (a b : Poly) : Poly := addPoly a b
/-- Routed alias of `subPoly`. See `addPolyFast`. -/
def subPolyFast (a b : Poly) : Poly := subPoly a b
/-- Routed alias of `pointwiseMul`. See `addPolyFast`. -/
def pointwiseMulFast (a b : Poly) : Poly := pointwiseMul a b
/-- Routed alias of `ntt`. See `addPolyFast`. -/
def nttFast (w : Poly) : Poly := ntt w
/-- Routed alias of `intt`. See `addPolyFast`. -/
def inttFast (w : Poly) : Poly := intt w

/-! The alias is the SAME OBJECT to the kernel — these are `rfl`, and they are what lets a caller be
retargeted onto the alias without disturbing a single proof about the pure def. -/
@[simp] theorem addPolyFast_eq : addPolyFast = addPoly := rfl
@[simp] theorem subPolyFast_eq : subPolyFast = subPoly := rfl
@[simp] theorem pointwiseMulFast_eq : pointwiseMulFast = pointwiseMul := rfl
@[simp] theorem nttFast_eq : nttFast = ntt := rfl
@[simp] theorem inttFast_eq : inttFast = intt := rfl

attribute [implemented_by fastAddPoly] addPolyFast
attribute [implemented_by fastSubPoly] subPolyFast
attribute [implemented_by fastPointwiseMul] pointwiseMulFast
attribute [implemented_by fastNtt] nttFast
attribute [implemented_by fastIntt] inttFast

/-! ### Twin differentials — each `fast…` twin vs an UNROUTED pure ground truth (non-vacuous).

⚠ These six are the ORIGINAL corpus and they are WEAK: measured over all 256 lanes, the largest
`sampleA[i] * sampleB[i]` is **4** and the largest `sampleA[i] + sampleB[i]` is **7**, against a
`2³²` truncation threshold and a `q = 8 380 417` reduction threshold. So the element-wise guards
below stay green against a `mulQu` written the naive 32-bit way, and against an `addQu` with its
`% qU` deleted — the exact two faults their docstring says they exist to catch. Both facts, and
twins that exhibit them, are named theorems in `Dregg2.Crypto.MlDsaRingTwinDifferential`, which
carries the full-range corpus these should have had. They are kept because they are still true and
still cheap, not because they are adequate. -/

-- The whole fast NTT multiply pipeline equals the pure negacyclic `schoolbookMul` (the load-bearing gate:
-- `ntt_computes_negacyclic_mul` computed with the fast twins on one side, pure `schoolbookMul` on the other).
#guard fastIntt (fastPointwiseMul (fastNtt sampleA) (fastNtt sampleB)) == schoolbookMul sampleA sampleB
-- Fast round-trip: `intt ∘ ntt = id` on a nonzero high-degree poly.
#guard fastIntt (fastNtt sampleA) == sampleA
-- The schoolbook twin equals the pure `schoolbookMul` byte-for-byte.
#guard fastSchoolbookMul sampleA sampleB == schoolbookMul sampleA sampleB
-- Element-wise twins vs the inline pure `Nat` formulas (`+`, `*`, `a+q−b`, all mod `q` — unrouted).
#guard (List.range 256).all (fun i => (fastAddPoly sampleA sampleB)[i]! == (sampleA[i]! + sampleB[i]!) % q)
#guard (List.range 256).all (fun i =>
  (fastSubPoly sampleA sampleB)[i]! == (sampleA[i]! + q - sampleB[i]!) % q)
#guard (List.range 256).all (fun i =>
  (fastPointwiseMul sampleA sampleB)[i]! == (sampleA[i]! * sampleB[i]!) % q)

end Dregg2.Crypto.MlDsaRing

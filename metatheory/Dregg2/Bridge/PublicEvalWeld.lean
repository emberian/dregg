import Dregg2.Bridge.MinaWrapFtEval0
-- ⚑ the DATA module, not the GATE (2026-08-09): only `PUBLIC_INPUT` is read here.
import Dregg2.Circuit.Emit.MinaWrapPublicCommData
import Dregg2.Circuit.Emit.MinaRealBlockGate
import Dregg2.Circuit.Emit.KimchiVerify
import Dregg2.Circuit.Emit.PastaBasePrime
import Dregg2.Circuit.Emit.PastaScalarPrime
/-!
# Dregg2.Bridge.PublicEvalWeld — the witnessed-inverse `p(ζ)` IS the shipped `publicEval`.

## What this closes

`MinaWrapFtEval0` §2 says it plainly: "inverses, WITNESSED rather than trusted. Nothing below
assumes the modulus is prime." §7 adds that recomputing `p(ζ)` "is `public_len` inverses, and §2's
witnessed device supplies them **without a `Field` instance**."

That device was the right call when there was no `Field (ZMod qN)` — and it is what
`MinaWrapFtEval0Weld` uses to recompute block 539508's `p(ζ)` and `p(ζω)` from the Wrap side's forty
public words. But it made `publicEvalAt` a **second spelling** of `KimchiVerify.publicEval`, and
nothing welded the two. That is the same shape `cipR_eq` / `ftEval0R_eq` exist to close for `cipR`
and `ftEval0R`, and `publicEval` had no such theorem: the real-block leg was evidence about
`publicEvalAt`, not about the shipped definition.

`Fact (Nat.Prime qN)` (`Dregg2/Circuit/Emit/PastaScalarPrime.lean`) makes the weld statable at the
field the Wrap side actually computes in.

## §1 is a gap this file found on the way

`powFast` — square-and-multiply, used for `ω^i`, `x^n`, `α^21` and the Fermat ladder `x^(m−2)`
throughout the Wrap leg AND in `EmitConformanceVectors` — had **no correctness theorem**. Its only
tie to `^` was `powFast_is_pow`, a `decide` on **four** small cases (`3^0`, `3^1`, `3^7`, `5^40`).
Four cases is not a ladder. `powFast_eq_pow` below is the theorem, for every monoid and every
exponent the fuel covers.

## Axiom hygiene

`#assert_axioms`-clean; no `sorry`, no `native_decide`.
-/

namespace Dregg2.Bridge.PublicEvalWeld

open Dregg2.Circuit.Emit.PastaField (pN qN)
open Dregg2.Bridge.MinaWrapFtEval0 (powFastAux powFast invCand invOk inv? publicEvalAt)
open Dregg2.Circuit.Emit.KimchiVerify (lagrangeSum publicEval)
open Dregg2.Bridge.MinaWrapFtEval0 (rootOfUnity)

set_option autoImplicit false

/-! ## §1 — `powFast` computes the power it names. -/

/-- The worker: `powFastAux fuel b e acc = acc · b^e` whenever the fuel covers the exponent. -/
theorem powFastAux_eq {R : Type} [Monoid R] (fuel : Nat) :
    ∀ (b : R) (e : Nat) (acc : R), e < 2 ^ fuel → powFastAux fuel b e acc = acc * b ^ e := by
  induction fuel with
  | zero =>
    intro b e acc h
    have he : e = 0 := by simpa using h
    subst he
    simp [powFastAux]
  | succ fuel ih =>
    intro b e acc h
    simp only [powFastAux]
    by_cases he : e = 0
    · subst he; simp
    · rw [if_neg he]
      have h2 : e / 2 < 2 ^ fuel := by
        rw [Nat.div_lt_iff_lt_mul (by norm_num)]
        simpa [pow_succ] using h
      rw [ih (b * b) (e / 2) _ h2]
      have hbb : (b * b) ^ (e / 2) = b ^ (2 * (e / 2)) := by
        rw [pow_mul]; norm_num [pow_two]
      rw [hbb]
      rcases Nat.mod_two_eq_zero_or_one e with h0 | h1
      · rw [if_neg (by omega)]
        have : 2 * (e / 2) = e := by omega
        rw [this]
      · rw [if_pos h1]
        have : 2 * (e / 2) + 1 = e := by omega
        rw [mul_assoc, ← pow_succ' b, this]

/-- **`powFast_eq_pow`** — the ladder IS the exponent, for every exponent the 512 bits of fuel
cover (which is every exponent this tree forms: the largest is `m − 2` at a 255-bit modulus).
⚑ This is what `powFast_is_pow`'s four `decide`d cases were standing in for. -/
theorem powFast_eq_pow {R : Type} [Monoid R] (b : R) (e : Nat) (h : e < 2 ^ 512) :
    powFast b e = b ^ e := by
  unfold powFast
  simpa using powFastAux_eq 512 b e 1 h

/-- The exponents the Wrap leg actually forms are all `< 2^512` by a wide margin — the largest is
`qN − 2`, a 255-bit number. Stated so a caller does not have to rediscover it. -/
theorem pasta_exponents_are_covered : pN - 2 < 2 ^ 512 ∧ qN - 2 < 2 ^ 512 := by
  have h : (2 : Nat) ^ 256 ≤ 2 ^ 512 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  exact ⟨lt_of_lt_of_le (by norm_num [pN]) h, lt_of_lt_of_le (by norm_num [qN]) h⟩

/-! ## §2 — the witnessed inverse IS the field inverse, at a prime modulus. -/

/-- `inv?` only ever returns a value it has CHECKED: `x · y = 1`. No primality needed for this
half — it is `invOk`'s whole point. -/
theorem inv?_mul_eq_one {m : Nat} {x y : ZMod m} (h : inv? x = some y) : x * y = 1 := by
  simp only [inv?] at h
  by_cases hb : invOk x (invCand x) = true
  · rw [if_pos hb] at h
    have : y = invCand x := by injection h.symm
    subst this
    simpa [invOk] using hb
  · rw [if_neg hb] at h
    exact absurd h (by simp)

/-- **`inv?_eq_inv`** — and at a prime modulus that check pins it to Mathlib's `⁻¹`. This is the
bridge between `MinaWrapFtEval0`'s deliberately `Field`-free device and the `[Field F]`-typed
shipped definitions. -/
theorem inv?_eq_inv {m : Nat} [Fact (Nat.Prime m)] {x y : ZMod m} (h : inv? x = some y) :
    y = x⁻¹ :=
  (inv_eq_of_mul_eq_one_right (inv?_mul_eq_one h)).symm

/-! ## §3 — the Lagrange fold: `publicEvalAt`'s accumulator IS `lagrangeSum`.

The fold below is `publicEvalAt`'s own body, not a mirror of it: §4 discharges the main statement
by `simp only [publicEvalAt]` onto exactly this shape. -/

theorem lagrange_fold_eq {m : Nat} [Fact (Nat.Prime m)] (omega x : ZMod m) (pub : List (ZMod m))
    (N : Nat) (hw : ∀ i, i < N → powFast omega i = omega ^ i) :
    ∀ (k : Nat), k ≤ N → ∀ (s0 s : ZMod m),
      (List.range k).foldl
        (fun acc i =>
          match acc with
          | none => none
          | some s =>
            match inv? (x - powFast omega i) with
            | none => none
            | some d => some (s + (-(pub.getD i 0)) * d * powFast omega i))
        (some s0) = some s →
      s = (List.range k).foldl
            (fun acc i => acc + (-(pub.getD i 0)) * omega ^ i * (x - omega ^ i)⁻¹) s0 := by
  intro k
  induction k with
  | zero => intro _ s0 s h; simpa using h.symm
  | succ k ih =>
    intro hk s0 s h
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at h ⊢
    -- the inner fold must have SUCCEEDED, or the step could not have produced a `some`
    cases hinner : (List.range k).foldl
        (fun acc i =>
          match acc with
          | none => none
          | some s =>
            match inv? (x - powFast omega i) with
            | none => none
            | some d => some (s + (-(pub.getD i 0)) * d * powFast omega i))
        (some s0) with
    | none => rw [hinner] at h; simp at h
    | some s' =>
      rw [hinner] at h
      rw [← ih (by omega) s0 s' hinner]
      dsimp only at h
      rw [hw k (by omega)] at h
      cases hd : inv? (x - omega ^ k) with
      | none => rw [hd] at h; simp at h
      | some d =>
        rw [hd] at h
        simp only [Option.some.injEq] at h
        rw [← h, inv?_eq_inv hd]
        ring

/-! ## §4 — the weld. -/

/-- **`publicEvalAt_is_publicEval`** — ⚑ whenever the witnessed device SUCCEEDS, its answer is the
shipped `KimchiVerify.publicEval`'s answer. So `MinaWrapFtEval0Weld`'s block-539508 checks —
`p(ζ)` and `p(ζω)` recomputed from the Wrap side's forty public words, plus the three
slot-tamper poles — are evidence about the SHIPPED definition, not about a second spelling of it.

`none` is a refusal and carries no claim: it is what the device returns at `x = ω^i`, where the
Lagrange form is undefined and where `publicEval` (following kimchi) returns 0 regardless. The
hypothesis is exactly that the device did not refuse.

The `powFast` side condition is discharged by `powFast_eq_pow` at any exponent under `2^512`. -/
theorem publicEvalAt_is_publicEval {m : Nat} [Fact (Nat.Prime m)]
    (n : Nat) (omega x : ZMod m) (pub : List (ZMod m)) (v : ZMod m)
    (hn : n < 2 ^ 512) (hlen : pub.length ≤ 2 ^ 512)
    (h : publicEvalAt n omega x pub = some v) :
    v = publicEval n omega x pub := by
  have hw : ∀ i, i < pub.length → powFast omega i = omega ^ i :=
    fun i hi => powFast_eq_pow omega i (lt_of_lt_of_le hi hlen)
  simp only [publicEvalAt] at h
  cases hnn : inv? ((n : Nat) : ZMod m) with
  | none => rw [hnn] at h; simp at h
  | some nInv =>
    rw [hnn] at h
    dsimp only at h
    -- destructure through `Option.map` rather than matching the fold syntactically: the fold's
    -- `let` is zeta-reduced by `simp only [publicEvalAt]`, so unification, not `rw`, is the tool.
    rcases Option.map_eq_some_iff.mp h with ⟨s, hs0, hv⟩
    have hs : s = lagrangeSum omega x pub :=
      lagrange_fold_eq omega x pub pub.length hw pub.length le_rfl 0 s hs0
    rw [← hv, hs, inv?_eq_inv hnn, powFast_eq_pow x n hn]
    simp only [publicEval]
    ring


/-! ## §5 — ⚑ THE SHIPPED DEFINITION, ON THE REAL BLOCK, AT THE DEPLOYED WRAP FIELD.

Everything above is generic. This is the point of it: `KimchiVerify.publicEval` — the `[Field F]`-
typed shipped definition — evaluated at `ZMod qN` on Mina devnet block 539508's forty public input
words, reproducing the `p(ζ)` that kimchi computed.

⚑ THIS COULD NOT BE WRITTEN YESTERDAY. `publicEval` needs `⁻¹`, so it needs a `Field`; `ZMod qN`
became one this morning. `MinaWrapFtEval0Weld`'s existing checks run `publicEvalAt`, the
witnessed-inverse spelling — and §4 is what makes those checks evidence about THIS definition. Here
the shipped definition is run directly, so the two routes to `p(ζ)` are both measured against
kimchi's own value rather than against each other. -/

/-- The block's forty public words in the Pallas SCALAR field. -/
def PUB : List (ZMod qN) :=
  Dregg2.Circuit.Emit.MinaWrapPublicCommGate.PUBLIC_INPUT.map (fun x => (x : ZMod qN))

#guard PUB.length == 40

/- ⚑ `p(ζ)` — the SHIPPED `publicEval` at `ZMod qN`, equal to the value kimchi computed. -/
#guard publicEval 16384 (rootOfUnity qN 14) Dregg2.Circuit.Emit.MinaRealBlockGate.ZETA PUB
       == Dregg2.Circuit.Emit.MinaRealBlockGate.PZ

/- …and `p(ζω)`, so a formula that matched at one point only is caught. -/
#guard publicEval 16384 (rootOfUnity qN 14)
         (Dregg2.Circuit.Emit.MinaRealBlockGate.ZETA * rootOfUnity qN 14) PUB
       == Dregg2.Circuit.Emit.MinaRealBlockGate.EVZW.getD 2 0

/- NON-VACUITY: every word is read. Moving slot 12 — the only slot the served block enters — and
slot 39, the last one, each move `p(ζ)`. A fold that stopped early passes the first and fails the
second. -/
#guard publicEval 16384 (rootOfUnity qN 14) Dregg2.Circuit.Emit.MinaRealBlockGate.ZETA
         (PUB.set 12 0) != Dregg2.Circuit.Emit.MinaRealBlockGate.PZ
#guard publicEval 16384 (rootOfUnity qN 14) Dregg2.Circuit.Emit.MinaRealBlockGate.ZETA
         (PUB.set 39 1) != Dregg2.Circuit.Emit.MinaRealBlockGate.PZ

/- …and the two spellings agree ON THE REAL BLOCK, which is §4 discharged at the deployed data
rather than only as a theorem. -/
#guard publicEvalAt 16384 (rootOfUnity qN 14) Dregg2.Circuit.Emit.MinaRealBlockGate.ZETA PUB
       == some (publicEval 16384 (rootOfUnity qN 14)
                 Dregg2.Circuit.Emit.MinaRealBlockGate.ZETA PUB)

#assert_axioms powFastAux_eq
#assert_axioms powFast_eq_pow
#assert_axioms pasta_exponents_are_covered
#assert_axioms inv?_mul_eq_one
#assert_axioms inv?_eq_inv
#assert_axioms lagrange_fold_eq
#assert_axioms publicEvalAt_is_publicEval

#assert_namespace_axioms Dregg2.Bridge.PublicEvalWeld

end Dregg2.Bridge.PublicEvalWeld

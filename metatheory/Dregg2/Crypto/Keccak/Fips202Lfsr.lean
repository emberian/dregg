/-
# `Dregg2.Crypto.Keccak.Fips202Lfsr` — the FIPS 202 Algorithm-5 round constants, in the KERNEL.

This file removes the LAST compiled-evaluation residual of the Keccak refinement chain.

## The problem it solves

`Dregg2.Crypto.Keccak.Fips202Spec` transcribes **NIST FIPS 202** §3.2.5 / Algorithm 5 (`rc(t)`, an
8-bit LFSR) and Algorithm 6 (`RC[ir]`, assembled from `rc(j + 7·ir)` at bit positions `2^j − 1`) as
`Fips202.rcBit` / `Fips202.rcLaneOf`. Both are written in `Id.run do` style with `for _ in [0:n]`
loops — i.e. over `Std.Legacy.Range`.

`Std.Legacy.Range.forIn` is defined by **well-founded** recursion (`Std.Legacy.Range.forIn'.loop`,
`Init/Data/Range/Basic.lean`). `WellFounded.fix` does **not** reduce under the kernel's `whnf`, so
`Fips202.rcBit t` is *opaque to the kernel* for every `t` with `t % 255 ≠ 0`. Measured on this tree:
`example : Fips202.rcBit 1 = false := by rfl` fails **instantly** with "not definitionally equal",
while `Fips202.rcBit 0 = true` (the early-return branch, no loop) succeeds. That is why the round
constant cross-check `Fips202Refine.rc_lanes_eq_exec` had to be closed by `native_decide`, leaking
`Lean.ofReduceBool` + `Lean.trustCompiler` into every theorem above `keccakRound`.

## What this file does

It gives the SAME LFSR a **structurally recursive** twin (`iterN` over `Nat`, which the kernel *does*
reduce), and proves the twin equal to the spec by a genuine `∀`:

* `rcBit_eq_rcBitRec : ∀ t, Fips202.rcBit t = rcBitRec t`
* `rcLaneOf_eq_rcLaneOfRec : ∀ ir z, Fips202.rcLaneOf ir z = rcLaneOfRec ir z`

Neither is a restatement-by-`rfl`: the spec side is the `Std.Legacy.Range` do-loop and the `Rec` side
is `Nat`-structural recursion, and the bridge is the honest induction `foldl_range'_eq_iterN`
(`List.foldl` over `List.range'` = `n`-fold iteration), composed with the core rewrite
`Std.Legacy.Range.forIn_eq_forIn_range'`.

The spec is NOT touched, NOT weakened, and NOT redefined to match anything executable: `Fips202.rcBit`
still *is* the Algorithm-5 transcription, and it is the LEFT-hand side of every bridge here.

With the loops gone, `decide` closes the 24-lane constant check **in the kernel** — no compiler, no
`ofReduceBool`. `#print axioms round_constants_are_lfsr` reports exactly
`[propext, Classical.choice, Quot.sound]`.

## Honest scope

`round_constants_are_lfsr` is a *finite* statement (24 rounds × 64 bits) — it is not a closed-form
theorem about the LFSR recurrence. But it is a **kernel-checked** finite statement: the Lean kernel
itself unfolds `Fips202.rcBit`'s recurrence 14 028 times and compares against the executable's `RC`
table. The trust boundary is the kernel, not the compiler + FFI. Elapsed: ~4.6 s for the whole file.

Cited: NIST FIPS 202, "SHA-3 Standard: Permutation-Based Hash and Extendable-Output Functions"
(Aug 2015, https://doi.org/10.6028/NIST.FIPS.202), §3.2.5 and Algorithms 5 and 6.
-/
import Dregg2.Crypto.Keccak
import Dregg2.Crypto.Keccak.Fips202Spec

namespace Dregg2.Crypto.Keccak.Fips202Lfsr

open Dregg2.Crypto.Keccak.Fips202 (rcBit rcLaneOf)

/-! ## The generic bridge: a `Std.Legacy.Range` for-loop is `n`-fold iteration.

Everything kernel-hostile in `Fips202.rcBit` is the `for _ in [0 : n]` loop. `Std.Legacy.Range`'s
`forIn` rewrites (core `@[simp]` lemma `forIn_eq_forIn_range'`) to a `forIn` over `List.range'`, and
a `forIn` whose body always `yield`s is a `List.foldl` (core `List.forIn_pure_yield_eq_foldl`). The
one lemma this file has to supply is that such a fold, over `List.range' i n`, is exactly `n`
applications of the body — a plain induction on `n`. -/

/-- `n`-fold application of `g`, by structural recursion on `n`. Unlike `Std.Legacy.Range.forIn`
(well-founded), this reduces under the kernel's `whnf`. -/
def iterN {α : Type} (g : α → α) : Nat → α → α
  | 0,     R => R
  | n + 1, R => iterN g n (g R)

/-- **The loop bridge.** A `List.foldl` of a state-only body over `List.range' i n` is `n`-fold
iteration of that body. Genuine `∀` over the body `g`, the start `i`, the length `n` and the initial
state. This is what lets a `Std.Legacy.Range` `for`-loop be replaced by something the kernel can
evaluate. -/
theorem foldl_range'_eq_iterN {α : Type} (g : α → α) (n : Nat) :
    ∀ (i : Nat) (init : α),
      List.foldl (fun b (_ : Nat) => g b) init (List.range' i n) = iterN g n init := by
  induction n with
  | zero => intro i init; rfl
  | succ k ih => intro i init; rw [List.range'_succ, List.foldl_cons, ih]; rfl

/-! ## FIPS 202 Algorithm 5, kernel-reducible.

`lfsrStep` is the body of `Fips202.rcBit`'s loop, character for character: FIPS 202 Algorithm 5
step 3, where `R` holds `R[0..7]`, `R[8]` after the "R = 0 || R" prepend is the old `R[7]`, and the
feedback taps fold `R[8]` into positions 0, 4, 5 and 6. `lfsrInit` is Algorithm 5 step 2's
`R = 10000000`. -/

/-- One clock of the FIPS 202 Algorithm-5 8-bit LFSR (`R[0]` is the output bit; `r8` is `R[8]`, i.e.
the old `R[7]`, after the Algorithm-5 "R = 0 ‖ R" prepend). Byte-for-byte the loop body of
`Fips202.rcBit`; `rcBit_eq_rcBitRec` proves that is not merely a claim. -/
def lfsrStep (R : Array Bool) : Array Bool :=
  let r8 := R[7]!
  let N : Array Bool := Array.replicate 8 false
  let N := N.set! 0 (xor false r8)     -- R[0] ⊕ R[8]
  let N := N.set! 1 (R[0]!)
  let N := N.set! 2 (R[1]!)
  let N := N.set! 3 (R[2]!)
  let N := N.set! 4 (xor (R[3]!) r8)   -- R[4] ⊕ R[8]
  let N := N.set! 5 (xor (R[4]!) r8)   -- R[5] ⊕ R[8]
  let N := N.set! 6 (xor (R[5]!) r8)   -- R[6] ⊕ R[8]
  let N := N.set! 7 (R[6]!)
  N

/-- FIPS 202 Algorithm 5 step 2: `R = 10000000`. -/
def lfsrInit : Array Bool := #[true, false, false, false, false, false, false, false]

/-- FIPS 202 Algorithm 5, kernel-reducible: `rc(t)` is `R[0]` after clocking the LFSR `t mod 255`
times from `10000000` (and `1` when `t mod 255 = 0`, Algorithm 5 step 1). -/
def rcBitRec (t : Nat) : Bool :=
  if t % 255 == 0 then true else (iterN lfsrStep (t % 255) lfsrInit)[0]!

/-- **Algorithm 5 bridge.** The FIPS 202 spec's `rc(t)` — the `Std.Legacy.Range` do-loop of
`Fips202.rcBit`, which the kernel cannot unfold — equals the structurally recursive `rcBitRec`, for
ALL `t : ℕ`. Proven, not computed: the loop is rewritten to a `List.foldl` by core lemmas and then
to `iterN` by `foldl_range'_eq_iterN`. -/
theorem rcBit_eq_rcBitRec (t : Nat) : rcBit t = rcBitRec t := by
  unfold rcBit rcBitRec
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, Id.run, bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl]
  split
  · rfl
  · rw [foldl_range'_eq_iterN]
    rfl

/-! ## FIPS 202 Algorithm 6, kernel-reducible. -/

/-- FIPS 202 Algorithm 6, kernel-reducible: the round-constant lane for round `ir`. Bit `z` is
`rc(j + 7·ir)` when `z = 2^j − 1` (`j = 0..6`), else `0`. Identical to `Fips202.rcLaneOf` except
that the `for j in [0:7]` `Std.Legacy.Range` loop is a loop over the literal list `List.range' 0 7`,
which the kernel reduces. -/
def rcLaneOfRec (ir : Nat) (z : Fin 64) : Bool := Id.run do
  for j in List.range' 0 7 do
    if z.val == 2 ^ j - 1 then
      return rcBitRec (j + 7 * ir)
  return false

/-- **Algorithm 6 bridge.** For ALL rounds `ir : ℕ` and ALL bit positions `z : Fin 64`, the FIPS 202
spec's round-constant lane equals its kernel-reducible twin. -/
theorem rcLaneOf_eq_rcLaneOfRec (ir : Nat) (z : Fin 64) : rcLaneOf ir z = rcLaneOfRec ir z := by
  unfold rcLaneOf rcLaneOfRec
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, rcBit_eq_rcBitRec]

/-! ## The payoff: the 24 round constants, checked BY THE KERNEL. -/

set_option maxRecDepth 4000000 in
/-- **The 24 Keccak-f[1600] round constants are the FIPS 202 Algorithm-5 LFSR output** — in the
`List.all` shape historically used by `Fips202Refine.rc_lanes_eq_exec` and unpacked by
`Fips202Round.rc_bit_match`.

Closed by **`decide`**, i.e. by the Lean KERNEL evaluating `Fips202.rcBit`'s own recurrence (via the
proven-equal `rcBitRec`) 14 028 times. It is NOT `native_decide`: no `Lean.ofReduceBool`, no
`Lean.trustCompiler`, no compiled evaluator in the trust boundary. -/
theorem rc_lanes_all :
    (List.range 24).all (fun ir =>
      (List.range 64).all (fun z =>
        rcLaneOf ir ⟨z % 64, Nat.mod_lt _ (by decide)⟩
          == (Dregg2.Crypto.Keccak.RC[ir]!).toBitVec.getLsbD z)) = true := by
  simp only [rcLaneOf_eq_rcLaneOfRec]
  decide

/-- **The headline, in `∀` form.** For every real Keccak-f[1600] round `ir < 24` and every bit
position `z`, the executable's precomputed round-constant word `RC[ir]` has at bit `z` exactly the
value the FIPS 202 §3.2.5 / Algorithm 5+6 LFSR prescribes.

This is the theorem the Keccak chain's last `native_decide` was standing in for. -/
theorem round_constants_are_lfsr (ir : Nat) (hir : ir < 24) (z : Fin 64) :
    rcLaneOf ir z = (Dregg2.Crypto.Keccak.RC[ir]!).toBitVec.getLsbD z.val := by
  have H := rc_lanes_all
  rw [List.all_eq_true] at H
  have H1 := H ir (List.mem_range.mpr hir)
  rw [List.all_eq_true] at H1
  have H2 := H1 z.val (List.mem_range.mpr z.isLt)
  rw [beq_iff_eq] at H2
  rw [← H2]
  congr 1
  apply Fin.ext
  simp [Nat.mod_eq_of_lt z.isLt]

end Dregg2.Crypto.Keccak.Fips202Lfsr

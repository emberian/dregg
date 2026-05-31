import Mathlib.Tactic
import Mathlib.Data.Int.GCD
import Mathlib.RingTheory.Int.Basic

/-
# Dregg2.Spike.TransferAir — soundness (and the precise *gap*) of the REAL Transfer AIR constraint

This is a **proof-of-method spike**: it shows that Lean can speak directly about the
constraint polynomials of the *real* circuit (`circuit/src/effect_vm/air.rs`) and prove,
rigorously and honestly, both **what the constraint guarantees** and **what it does not**.

## The exact real constraint (air.rs:473–486, verified against source)

```
c_transfer_lo  = s_transfer * (new_bal_lo - old_bal_lo - amount + 2*direction*amount)
c_transfer_hi  = s_transfer * (new_bal_hi - old_bal_hi)          // hi limb unchanged
c_transfer_dir = s_transfer * direction * (direction - 1)        // direction boolean
```

For an *active* transfer the selector `s_transfer = 1`, so a satisfying trace makes the
factor in parentheses equal to `0` **in the field** `BabyBear`. We model "equal to 0 in the
field" as the divisibility statement `p ∣ (·)` over `ℤ`, where
`p = 2013265921 = 15 * 2^27 + 1` is the BabyBear prime. (This is exactly the meaning of an
AIR constraint: the polynomial vanishes on the trace, i.e. its value is `0 mod p`.)

direction `0 = in` (add), `1 = out` (subtract):
  `new_bal_lo = old_bal_lo + amount * (1 - 2*direction)`.

Per source (air.rs:370–420): the limbs are **NOT range-checked in-circuit**, and the
subtraction **wraps mod p** if `amount > old_balance`. The only defense is the *off-circuit*
executor re-deriving the final state and rejecting out-of-range limbs.

## What is / isn't here
* `transfer_out_sound`, `transfer_in_sound`: **with** the off-circuit range + no-wrap
  hypotheses made explicit, the constraint pins down the unique integer balance update.
* `transfer_dir_boolean`: the direction-boolean constraint forces `dir ∈ {0,1}`.
* `transfer_underflow_attack`: **without** those hypotheses, the constraint is satisfied by a
  *wrapped* value `p-1`. This is the air.rs:402 gap, made formal.

NOTE (per-cell / per-row scope): every theorem below is about a **single cell on a single
row** — `±amount` applied to one balance. Two-party *conservation* (Σ of balances unchanged
across a transfer) is a **turn-level / net-delta** property and is **NOT** expressed by this
single constraint. We do not, and cannot, claim it here.
-/

namespace Dregg2.Spike.TransferAir

/-- The BabyBear prime `p = 15 * 2^27 + 1`. -/
def p : ℤ := 2013265921

/-- Sanity: the modulus is what the source says. -/
theorem p_value : p = 15 * 2 ^ 27 + 1 := by decide

/-- `2^30`, the limb width for `balance_lo` / `amount` (air.rs:372). It is `< p`. -/
theorem two_pow_30_lt_p : (2 : ℤ) ^ 30 < p := by decide

/--
The Transfer-lo constraint polynomial *value* (air.rs:474), as an integer:
`new - old - amount + 2*dir*amount`.
With `dir = 0` this is `new - old - amount` (an *add* must hold);
with `dir = 1` this is `new - old + amount` (a *subtract* must hold).
-/
def transferLo (old new amount dir : ℤ) : ℤ :=
  new - old - amount + 2 * dir * amount

/--
An *active* (`s_transfer = 1`) Transfer row **satisfies** the lo-constraint iff the
polynomial value is `0` in the field, i.e. `p ∣ transferLo …`. (For `s_transfer = 0` the
constraint is vacuous; the active case is the only interesting one.)
-/
def Sat (old new amount dir : ℤ) : Prop := p ∣ transferLo old new amount dir

/--
The direction-boolean constraint polynomial (air.rs:484): `dir * (dir - 1)`.
A satisfying row makes this `0` in the field.
-/
def SatDir (dir : ℤ) : Prop := p ∣ dir * (dir - 1)

/-- A value is a *canonical 30-bit limb* if it lies in `[0, 2^30)`. -/
def InRange30 (x : ℤ) : Prop := 0 ≤ x ∧ x < 2 ^ 30

/-
The single load-bearing arithmetic lemma: if `p` divides an integer `d` whose magnitude is
strictly below `p`, then `d = 0`. (`p` is prime but we only need `p > |d|`.)
-/
private theorem eq_zero_of_dvd_of_abs_lt {d : ℤ} (hdvd : p ∣ d)
    (hlo : -p < d) (hhi : d < p) : d = 0 := by
  obtain ⟨k, hk⟩ := hdvd
  -- d = p * k, with -p < p*k < p and p > 0 forces k = 0, hence d = 0.
  have hp : p = 2013265921 := rfl
  rw [hp] at hk hlo hhi
  omega

/--
**THEOREM `transfer_out_sound`.** An *outgoing* transfer (`dir = 1`, subtract) that satisfies
the in-circuit constraint, whose limbs are canonical 30-bit values, and for which the
executor's off-circuit **no-underflow** check (`amount ≤ old`) holds, performs exactly the
integer update `new = old - amount`.

This is the *positive* result: given the off-circuit guards, the AIR constraint pins the
unique correct successor balance.
-/
theorem transfer_out_sound
    (old new amount : ℤ)
    (hold : InRange30 old) (hnew : InRange30 new) (hamt : InRange30 amount)
    (hno_underflow : amount ≤ old)            -- air.rs:409 off-circuit defense
    (hsat : Sat old new amount 1) :
    new = old - amount := by
  -- For dir = 1: transferLo = new - old - amount + 2*amount = new - old + amount.
  -- So p ∣ (new - old + amount) = p ∣ (new - (old - amount)).
  obtain ⟨hold0, hold1⟩ := hold
  obtain ⟨hnew0, hnew1⟩ := hnew
  obtain ⟨hamt0, hamt1⟩ := hamt
  have hpw : (2 : ℤ) ^ 30 < p := two_pow_30_lt_p
  unfold Sat at hsat
  have hd : p ∣ (new - (old - amount)) := by
    have heq : transferLo old new amount 1 = new - (old - amount) := by
      unfold transferLo; ring
    rwa [heq] at hsat
  -- new ∈ [0,2^30), old - amount ∈ [0,2^30) (by no-underflow), both ⊂ [0,p), so |Δ| < p.
  have := eq_zero_of_dvd_of_abs_lt hd (by omega) (by omega)
  omega

/--
**THEOREM `transfer_in_sound`.** An *incoming* transfer (`dir = 0`, add) that satisfies the
constraint, has canonical 30-bit limbs, and for which the off-circuit **no-overflow** check
(`old + amount < 2^30`, so the result still fits the lo limb) holds, performs exactly
`new = old + amount`.
-/
theorem transfer_in_sound
    (old new amount : ℤ)
    (hold : InRange30 old) (hnew : InRange30 new) (hamt : InRange30 amount)
    (hno_overflow : old + amount < 2 ^ 30)    -- result fits the single lo limb
    (hsat : Sat old new amount 0) :
    new = old + amount := by
  obtain ⟨hold0, hold1⟩ := hold
  obtain ⟨hnew0, hnew1⟩ := hnew
  obtain ⟨hamt0, hamt1⟩ := hamt
  have hpw : (2 : ℤ) ^ 30 < p := two_pow_30_lt_p
  unfold Sat at hsat
  have hd : p ∣ (new - (old + amount)) := by
    have heq : transferLo old new amount 0 = new - (old + amount) := by
      unfold transferLo; ring
    rwa [heq] at hsat
  have := eq_zero_of_dvd_of_abs_lt hd (by omega) (by omega)
  omega

/--
**THEOREM `transfer_dir_boolean`.** The direction-boolean constraint (air.rs:484), together
with the assumption that `dir` is given by its canonical field representative
(`0 ≤ dir < p`), forces `dir = 0 ∨ dir = 1`.

(Without canonicity the field admits `dir = 0` and `dir = 1` and *only* those as residues;
any integer with `dir ≡ 0` or `dir ≡ 1 (mod p)` satisfies it, which is exactly the two field
values. The canonical-rep hypothesis just selects the unique integer witness per class.)
-/
theorem transfer_dir_boolean
    (dir : ℤ) (hlo : 0 ≤ dir) (hhi : dir < p)
    (hsat : SatDir dir) :
    dir = 0 ∨ dir = 1 := by
  -- p ∣ dir*(dir-1); p prime ⇒ p ∣ dir ∨ p ∣ (dir-1). With 0 ≤ dir < p that forces
  -- dir = 0 or dir = 1.
  unfold SatDir at hsat
  have hp : p = 2013265921 := rfl
  rw [hp] at hhi
  have hprime : Prime p := by rw [hp]; norm_num
  rcases hprime.dvd_mul.mp hsat with hdvd | hdvd
  · -- p ∣ dir, 0 ≤ dir < p ⇒ dir = 0
    left
    obtain ⟨m, hm⟩ := hdvd
    rw [hp] at hm; omega
  · -- p ∣ (dir - 1), 0 ≤ dir < p ⇒ dir - 1 ∈ (-p, p) ⇒ dir - 1 = 0
    right
    obtain ⟨m, hm⟩ := hdvd
    rw [hp] at hm; omega

/--
**THEOREM `transfer_underflow_attack` — THE GAP (air.rs:398–420), formalized.**

*Without* the off-circuit range / no-underflow hypothesis, the in-circuit constraint is
satisfied by a **wrapped** value. Concretely, an outgoing transfer of `amount = 1` from a
balance of `old = 0` admits `new = p - 1` as a satisfying witness, even though the *intended*
integer result `0 - 1 = -1` is negative (an underflow that the field silently wraps to `p-1`).

The constraint `Sat 0 (p-1) 1 1` holds (the polynomial value is `-p`, divisible by `p`), yet
`p - 1 ≠ 0 - 1`. So **the Transfer AIR constraint alone does NOT imply a sound,
non-wrapping balance update.**

Consequence (precise): soundness of the balance update requires an *in-circuit range proof*
that the result fits in 30 bits / is non-negative (the bit-decomposition / lookup argument
that **W9-RANGECHECK** adds; air.rs:386, air.rs:415 TODOs). Until then the property is held
only by the off-circuit executor re-derivation (air.rs:409).
-/
theorem transfer_underflow_attack :
    Sat 0 (p - 1) 1 1 ∧ (p - 1) ≠ (0 - 1 : ℤ) := by
  refine ⟨?_, ?_⟩
  · -- transferLo 0 (p-1) 1 1 = (p-1) - 0 - 1 + 2*1*1 = p - 1 - 1 + 2 = p, and p ∣ p.
    unfold Sat
    have h : transferLo 0 (p - 1) 1 1 = p := by unfold transferLo p; decide
    rw [h]
  · decide

/-!
## Verdict (proof-of-method, for the full 54-effect direction)

* **Feasibility: confirmed.** Lean speaks about the real AIR polynomials with zero
  impedance: a constraint is `p ∣ poly`, soundness is `(divisibility ∧ off-circuit guards) →
  integer-equation`, and `omega` closes the bounded-residue step once `poly` is `ring`-normalized.
* **Cost: low per linear/affine constraint.** Each such effect needs ~one `transferLo`-style
  `def`, a one-line `ring` rewrite, and the shared `eq_zero_of_dvd_of_abs_lt` lemma — call it a
  dozen lines. The 54-effect bill is dominated by *non-linear* / *commitment* constraints
  (Poseidon2, Merkle, lookups), not by the affine balance algebra modeled here.
* **Honest scope: the spike also *prices the gaps*.** The same machinery that proves soundness
  proves the **underflow attack** as a theorem — so doing this for all 54 effects yields, for
  free, a precise ledger of which guarantees are in-circuit vs. off-circuit (executor / future
  W9-RANGECHECK). That dual ability — prove the guarantee AND exhibit the gap — is the real
  value of the full-Lean-circuit direction.
-/

end Dregg2.Spike.TransferAir

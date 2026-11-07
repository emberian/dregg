/-
# Dregg2.Bridge.MinaVrfThreshold — Samasika's VRF LEADER ELECTION threshold, in Lean.

⚑ **SUBSTRATE, SAID OUT LOUD.** This file authors **NO AIR**. It is pure `Nat`/`Int`/`Bool` Lean.
Mina's threshold does have an in-circuit life (`Threshold.Checked.is_satisfied`,
`consensus_vrf.ml:346-381`, proved for every block by the blockchain SNARK), but what is authored
here is the *unchecked* decision procedure — `Threshold.is_satisfied`, `consensus_vrf.ml:326-344`
— which is what an off-circuit checker runs. Nothing here is a `Builder` gadget and nothing here
belongs in Rust. An in-circuit version on our side would be a Lean-authored `def`-generator plus
forcing lemmas (House Law #1); it does not exist and this file does not pretend to be it.

## The rule, exactly

A delegator wins a slot when

    vrf_output / 2^253  ≤  c · (1 − (1 − f)^(my_stake / total_stake))

with `c = 2^0 = 1` and `f = 3/4`, so `base = 1 − f = 1/4`. The comment above the OCaml
(`consensus_vrf.ml:323-325`) writes the divisor as `2^256`; the code divides by
`2^Output.Truncated.length_in_bits` and that is **253**, not 256 —
`length_in_bits = min 256 (Field.size_in_bits − 2)` (`consensus_vrf.ml:208`) and Tick is Pasta Fp
with `size_in_bits = 255`. openmina carries the corrected value with the OCaml derivation quoted
in a comment (`crates/vrf/src/threshold.rs:183-186`, `crates/ledger/src/proofs/block.rs:765`).

⚑ `c` is not a rounding detail that got dropped: `c_bias` (`consensus_vrf.ml:159-161`) implements
multiplication by `c = 2^i` as *dropping `i` low bits of the VRF output*, and at the production
value `i = 0` it is the identity. So the `c` in the formula is genuinely absent from the deployed
arithmetic rather than silently folded in.

**`1 − base^x` is NOT computed in closed form.** It is a truncated Taylor series over fixed-point
rationals — `Snarky_taylor.Exp` (`src/lib/snarky_taylor/snarky_taylor.ml:107-249`) — because it
has to be computable in a SNARK. §1 reproduces its parameter derivation rather than asserting the
numbers, and §2 proves the derivation lands on the constants openmina hardcodes.

## SOURCES

Canonical (OCaml), `~/dev/mina`:

| object | file:line |
|---|---|
| `Threshold.is_satisfied` (unchecked) | `src/lib/consensus/vrf/consensus_vrf.ml:326-344` |
| `Threshold.Checked.is_satisfied` (in-circuit) | `src/lib/consensus/vrf/consensus_vrf.ml:346-381` |
| `f = 3/4`, `base = 1 − f` | `src/lib/consensus/vrf/consensus_vrf.ml:313,315` |
| `c = 2^0`, `c_bias` | `src/lib/consensus/vrf/consensus_vrf.ml:157,159-161` |
| `Output.Truncated.length_in_bits`, `to_fraction` | `src/lib/consensus/vrf/consensus_vrf.ml:208,228-234` |
| `Exp.params` / `bit_params` / `terms_needed` / `log` | `src/lib/snarky_taylor/snarky_taylor.ml:147-193,133-145,55-65,42-49` |
| `Exp.Unchecked.one_minus_exp` | `src/lib/snarky_taylor/snarky_taylor.ml:195-211` |
| `Vrf.Checked.check` (where stake and total enter) | `src/lib/consensus/proof_of_stake.ml:747-772` |
| `Vrf.check` (the native producer loop) | `src/lib/consensus/proof_of_stake.ml:849-911` |
| VRF `eval` = `H(m, sk·H₂(m))` | `src/lib/vrf_lib/integrated.ml:92-95` |
| VRF message `(global_slot, seed, delegator)` | `src/lib/consensus/vrf/consensus_vrf.ml:76-118` |

Second, independent rendering (openmina, `~/dev/mina-rust`): native threshold
`crates/vrf/src/threshold.rs:15-96`; in-circuit `crates/ledger/src/proofs/block.rs:746-770`;
the hardcoded parameters `crates/ledger/src/proofs/block.rs:317-345`; the VRF itself
`crates/vrf/src/lib.rs:110-163` with hash-to-group `crates/vrf/src/message.rs:34-88`.

## THE VRF ITSELF IS NOT IN THIS FILE, AND THAT IS THE SCOPE FACT

`Vrf.eval sk m = H_MinaVrfOutput(m ‖ (sk · H_MinaVrfMessage→group(m)).x ‖ …y)` on Pallas
(`integrated.ml:92-95`) — Poseidon over Pasta plus a group map. Modelling *that* means modelling
Poseidon and the Pallas group map, which live elsewhere in this tree
(`Dregg2/Circuit/Emit/Pasta*.lean`, `PastaPoseidon.lean`) and are not re-derived here. What this
file authors is the part the threshold rule actually decides with: the comparison against the
stake-scaled bound, given an already-computed 253-bit VRF output.

⚑ And there is a harder fact than that, in §5: the threshold is only half of leader election, and
the other half is not something a light client holds.
-/
import Dregg2.Tactics

set_option autoImplicit false
set_option maxRecDepth 40000

namespace Dregg2.Bridge.MinaVrfThreshold

/-! ## §1 — The fixed-point Taylor parameters, DERIVED rather than asserted.

`Snarky_taylor.Exp.params ~base:(1/4) ~field_size_in_bits:255` (`consensus_vrf.ml:317-319`)
computes, at OCaml module-initialisation time:

* `abs_log_base = |log(1/4)|`, where `log` is the 100-term series
  `Σ_{i=1}^{100} (−1)^{i+1} (x−1)^i / i` (`snarky_taylor.ml:42-49`) — NOT the real logarithm;
* `(per_term_precision, terms_needed, total_precision)` from `bit_params`
  (`snarky_taylor.ml:133-145`);
* coefficients `⌊2^per_term_precision · (|log base|^i / i!)⌋`, alternating in sign, with the `i=1`
  term split into a whole part and a fraction (`snarky_taylor.ml:163-186`).

Everything below is integer arithmetic over an *unnormalised* common denominator, so no rational
normalisation (and no `Nat.gcd`) is needed to evaluate it. `absLogNum / absLogDen` is exactly the
OCaml's `abs_log_base`. -/

/-- `n!`, written out so kernel reduction stays on GMP-backed `Nat` multiplication. -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- Common denominator for the 100-term `log` series at `x = 1/4`: `4^100 · 100!`. Using `100!`
rather than `lcm(1..100)` keeps the derivation free of `Nat.gcd`, whose well-founded recursion the
kernel does not reduce cheaply; it is a larger denominator for the same exact rational. -/
def absLogDen : Nat := 4 ^ 100 * fact 100

/-- Numerator of `|log(1/4)|` under `absLogDen`. With `a = x - 1 = -3/4` every term of
`Sum (-1)^(i+1) a^i / i` is `-(3/4)^i / i`, so the absolute value is `Sum (3/4)^i / i`. -/
def absLogNum : Nat :=
  ((List.range 100).map (fun j => 3 ^ (j + 1) * 4 ^ (99 - j) * (fact 100 / (j + 1)))).foldl (· + ·) 0

/-- `per_term_precision`, the bit precision of every coefficient AND of the stake fraction
(`snarky_taylor.ml:142`, used at `consensus_vrf.ml:335`). -/
def perTermPrecision : Nat := 20

/-- `terms_needed` — the Taylor series is truncated after this many terms
(`snarky_taylor.ml:144`, and `terms_needed + 1` for the linear whole part at `:138-141`). -/
def termsNeeded : Nat := 11

/-- `total_precision`, the `k` that `bit_params` maximises (`snarky_taylor.ml:144`). -/
def totalPrecision : Nat := 16

/-- `floor(2^perTermPrecision * |log base|^i / i!)` — `bignum_as_fixed_point`
(`snarky_taylor.ml:12-14`) applied to the coefficient (`snarky_taylor.ml:169-171`). -/
def taylorCoeffRaw (i : Nat) : Nat :=
  (2 ^ perTermPrecision * absLogNum ^ i) / (absLogDen ^ i * fact i)

/-- The whole part of the linear coefficient, split out as `snarky_taylor.ml:173-178` does. It is
`1` here, i.e. `Coeff_integer_part.One` / openmina's `CoeffIntegerPart::One`. -/
def linearTermIntegerPart : Nat := absLogNum / absLogDen

/-- The coefficient list Mina actually uses: `i = 1` contributes only its FRACTIONAL part (the
whole part is carried separately), the rest contribute in full. -/
def taylorCoeff (i : Nat) : Nat :=
  if i = 1 then taylorCoeffRaw 1 - linearTermIntegerPart * 2 ^ perTermPrecision
  else taylorCoeffRaw i

def derivedCoefficients : List Nat := (List.range termsNeeded).map (fun j => taylorCoeff (j + 1))

/-! ## §2 — The derivation lands on the deployed constants.

openmina hardcodes the coefficient array (`crates/ledger/src/proofs/block.rs:317-345`) because
the circuit cannot compute it. Re-deriving it from `f = 3/4` alone and getting the same eleven
integers is the check that neither side invented a number. -/

/-- **The eleven deployed coefficients, derived.** Byte-for-byte openmina's `COEFFICIENTS`
(`block.rs:317-328`), signs alternating `Pos, Neg, …` from `i = 1`. -/
theorem derivedCoefficients_are_the_deployed_ones :
    derivedCoefficients =
      [405058, 1007582, 465602, 161365, 44739, 10337, 2047, 354, 54, 7, 0] := by decide +kernel

/-- The linear whole part is `1` — openmina's `CoeffIntegerPart::One` (`block.rs:345`). -/
theorem linearTermIntegerPart_is_one : linearTermIntegerPart = 1 := by decide +kernel

/-- `bit_params` maximises `k` subject to `(n+1)·(⌈log₂ n⌉ + k) < field_size_in_bits`
(`snarky_taylor.ml:143`). At the deployed `terms_needed = 11` and `field_size_in_bits = 255` the
chosen `k = 16` satisfies the guard and `k = 17` does not — which is what pins
`per_term_precision = 20`. -/
theorem bit_params_is_maximal :
    termsNeeded * perTermPrecision + perTermPrecision < 255 ∧
    ¬ (12 * 21 + 21 < 255) ∧
    perTermPrecision = 4 + totalPrecision := by decide +kernel

/-! ## §3 — The threshold predicate.

`is_satisfied` (`consensus_vrf.ml:326-344`):

* `input = ⌊2^20 · my_stake / total_stake⌋ / 2^20` — the stake fraction, QUANTISED to
  `per_term_precision` bits (`:330-338`);
* `rhs = one_minus_exp params input` = `Σ_{i=1}^{11} ±cᵢ·inputⁱ / 2^20 + 1·input`
  (`snarky_taylor.ml:195-211`);
* `lhs = vrf_output / 2^253` (`:228-234, 343`);
* the verdict is `lhs ≤ rhs` (`:344`).

Both the OCaml (`Bignum`) and openmina's native path (`BigRational`) evaluate this in EXACT
rationals, and the circuit's `Floating_point` accumulates precision rather than truncating
(`snarky_taylor.ml:213-249`), so all three agree with the exact integer form below. Put over the
common denominator `2^240 = 2^(20·12)`, `rhs = thresholdNumerator / 2^240`, and

    vrf / 2^253 ≤ N / 2^240   ⟺   vrf ≤ N · 2^13. -/

/-- `⌊2^20 · my_stake / total_stake⌋` — the quantised stake fraction, numerator over `2^20`
(`consensus_vrf.ml:330-338`). -/
def stakeQuantum (myStake totalStake : Nat) : Nat :=
  2 ^ perTermPrecision * myStake / totalStake

/-- `one_minus_exp params (n / 2^20)`, as an integer over the common denominator `2^240`. The
final `+ n · 2^220` is the linear whole part (`snarky_taylor.ml:208-211`). -/
def polyNumerator (x : Int) : Int :=
  405058 * x * 2 ^ 200
  - 1007582 * x ^ 2 * 2 ^ 180
  + 465602 * x ^ 3 * 2 ^ 160
  - 161365 * x ^ 4 * 2 ^ 140
  + 44739 * x ^ 5 * 2 ^ 120
  - 10337 * x ^ 6 * 2 ^ 100
  + 2047 * x ^ 7 * 2 ^ 80
  - 354 * x ^ 8 * 2 ^ 60
  + 54 * x ^ 9 * 2 ^ 40
  - 7 * x ^ 10 * 2 ^ 20
  + x * 2 ^ 220

/-- The right-hand side of the threshold, over `2^240`. -/
def thresholdNumerator (myStake totalStake : Nat) : Int :=
  polyNumerator ((stakeQuantum myStake totalStake : Nat) : Int)

/-- **`Threshold.is_satisfied`.** `vrfOutput` is the 253-bit truncated VRF output read
little-endian (`consensus_vrf.ml:228-234`); `myStake` is the winner account's balance and
`totalStake` the epoch ledger's `total_currency` (`proof_of_stake.ml:765-772`). -/
def isSatisfied (vrfOutput myStake totalStake : Nat) : Bool :=
  (vrfOutput : Int) ≤ thresholdNumerator myStake totalStake * 2 ^ 13

/-- `isSatisfied` as a function equation. Proofs `rw` with this, never `simp [isSatisfied]`:
since v4.35 `Decidable.decide` is a structure projection, and the kernel checking
`isSatisfied v s t ≡ decide (…)` pointwise (the equation lemma `simp`/`unfold` generate, or a
`simpa` closing step) unfolds the projection first and whnfs `Int.decLe` over the symbolic
degree-10 polynomial: deep recursion after minutes and tens of GB. The function-level equation is
closed by unfolding `isSatisfied` once. -/
theorem isSatisfied_def :
    isSatisfied = fun (vrfOutput myStake totalStake : Nat) =>
      decide ((vrfOutput : Int) ≤ thresholdNumerator myStake totalStake * 2 ^ 13) := rfl

/-- The VRF output is 253 bits, so this is its exclusive upper bound
(`consensus_vrf.ml:208`, openmina `block.rs:765`). -/
def vrfOutputBound : Nat := 2 ^ 253

/-! ## §4 — What is true of it. -/

/-- Sanity against the closed form the code is approximating: at a 1% stake the bound is
`0.0137662…`, against a true `1 − (1/4)^0.01 = 0.0137672…`. Stated as an exact rational
sandwich so it cannot rot. -/
theorem threshold_at_one_percent_is_near_the_closed_form :
    137662 * (2:Int) ^ 240 < polyNumerator 10485 * 10 ^ 7 ∧
    polyNumerator 10485 * 10 ^ 7 < 137673 * (2:Int) ^ 240 := by
  refine ⟨?_, ?_⟩ <;> · simp only [polyNumerator]; norm_num

/-- **A smaller VRF output never loses a slot a larger one wins.** Immediate, but it is the
direction that makes the rule a threshold at all. -/
theorem isSatisfied_antitone_in_output (v v' s t : Nat) (h : v ≤ v')
    (hw : isSatisfied v' s t = true) : isSatisfied v s t = true := by
  have hw' : (v' : Int) ≤ thresholdNumerator s t * 2 ^ 13 := by
    rw [isSatisfied_def] at hw; exact of_decide_eq_true hw
  rw [isSatisfied_def]
  exact decide_eq_true (le_trans (Int.ofNat_le.mpr h) hw')

/-- The quantised stake fraction is monotone in stake. -/
theorem stakeQuantum_monotone (s s' t : Nat) (h : s ≤ s') :
    stakeQuantum s t ≤ stakeQuantum s' t :=
  Nat.div_le_div_right (Nat.mul_le_mul_left _ h)

/-- The stake fraction never exceeds one whole unit, when stake is a share of the total. -/
theorem stakeQuantum_le (s t : Nat) (h : s ≤ t) (ht : 0 < t) :
    stakeQuantum s t ≤ 2 ^ perTermPrecision := by
  simp only [stakeQuantum]
  calc 2 ^ perTermPrecision * s / t ≤ 2 ^ perTermPrecision * t / t :=
        Nat.div_le_div_right (Nat.mul_le_mul_left _ h)
    _ = 2 ^ perTermPrecision := by rw [Nat.mul_div_cancel _ ht]

/-! ### §4.1 — Monotonicity in stake.

`polyNumerator` is a degree-11 alternating polynomial; that it INCREASES on `[0, 2^20]` is not
visible from its coefficients, which decrease and change sign. It is proved here by exhibiting
the forward difference in the **Bernstein basis** of `[0, 2^20]`: if

    2^(20·9) · (P(n+1) − P(n)) = Σ_{k=0}^{9} b_k · n^k · d^(9−k)   with   n + d = 2^20

and every `b_k ≥ 0`, then the difference is non-negative for every `n` in range, because `n` and
`d` are. The nine `b_k` below are the Bernstein coefficients; the identity is a polynomial one and
`ring` checks it. -/

/-- The ten Bernstein coefficients of `2^180 · (P(n+1) − P(n))` on `[0, 2^20]`. They are all
NON-NEGATIVE, and stating them as `Nat` is exactly that fact: there is nothing to prove about
their signs because the type carries it. -/
def bernSum (n d : Nat) : Nat :=
    2335898232914131491323571459937023044974866445223670776580046585856 * d ^ 9
  + 17784842539804082656473606967457035808895229069854228630328151375872 * n * d ^ 8
  + 60430983151626946885015425712183839681299832273687025774849729495040 * n ^ 2 * d ^ 7
  + 120219528967236829099017045758407536499029614890741055729035431116800 * n ^ 3 * d ^ 6
  + 154253996269292674314507551400063861212044452921526187942171587379200 * n ^ 4 * d ^ 5
  + 132345991260245183763972812503803591026694239532884408291446879158272 * n ^ 5 * d ^ 4
  + 75908927850135114306923667261959905398405592290711873321242118324224 * n ^ 6 * d ^ 3
  + 28060704782306679531787049558424860104571500040935200753999258058752 * n ^ 7 * d ^ 2
  + 6065338644369977628928755914440480843420293111914496616701134635008 * n ^ 8 * d
  + 583964113082971446129169023145622859572276954438796231236425613312 * n ^ 9

/-- The Bernstein identity for the forward difference. `ring` checks it; the content is that a
degree-9 polynomial with mixed signs in the monomial basis has ONLY non-negative coefficients in
the Bernstein basis of `[0, 2^20]`. -/
theorem polyNumerator_diff_bernstein (n d : Nat) (h : n + d = 2 ^ 20) :
    (2:Int) ^ 180 * (polyNumerator ((n : Int) + 1) - polyNumerator (n : Int))
      = ((bernSum n d : Nat) : Int) := by
  have hd : (d : Int) = 2 ^ 20 - (n : Int) := by omega
  simp only [polyNumerator, bernSum, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    hd]
  push_cast [hd]
  ring

/-- **MORE STAKE NEVER LOSES A SLOT YOU WOULD HAVE WON**, in the stake-fraction variable. -/
theorem polyNumerator_step (j : Nat) (hj : j ≤ 2 ^ 20) :
    polyNumerator (j : Int) ≤ polyNumerator ((j : Int) + 1) := by
  have hd : j + (2 ^ 20 - j) = 2 ^ 20 := by omega
  have hid := polyNumerator_diff_bernstein j (2 ^ 20 - j) hd
  have hpos : (0:Int) < 2 ^ 180 := by decide +kernel
  have hnn : (0:Int) ≤ (2:Int) ^ 180 * (polyNumerator ((j : Int) + 1) - polyNumerator (j : Int)) := by
    rw [hid]; exact Int.natCast_nonneg _
  have hsub : (0:Int) ≤ polyNumerator ((j : Int) + 1) - polyNumerator (j : Int) :=
    Int.le_of_mul_le_mul_left (by simpa using hnn) hpos
  exact Int.sub_nonneg.mp hsub

theorem polyNumerator_monotone (n m : Nat) (h : n ≤ m) (hm : m ≤ 2 ^ 20) :
    polyNumerator (n : Int) ≤ polyNumerator (m : Int) := by
  induction m with
  | zero => simp_all
  | succ j ih =>
      rcases Nat.lt_or_ge n (j + 1) with hlt | hge
      · have hj : n ≤ j := Nat.lt_succ_iff.mp hlt
        have hjb : j ≤ 2 ^ 20 := Nat.le_of_succ_le hm
        refine le_trans (ih hj hjb) ?_
        have := polyNumerator_step j hjb
        have hc : ((j + 1 : Nat) : Int) = (j : Int) + 1 := by push_cast; ring
        rw [hc]; exact this
      · have : n = j + 1 := Nat.le_antisymm h hge
        rw [this]

/-- **The headline, at the level of the decision.** A delegator with more stake wins every slot a
delegator with less stake would have won, on the same VRF output and the same epoch ledger. -/
theorem more_stake_never_loses (v s s' t : Nat) (hs : s ≤ s') (hs' : s' ≤ t) (ht : 0 < t)
    (hw : isSatisfied v s t = true) : isSatisfied v s' t = true := by
  have hw' : (v : Int) ≤ thresholdNumerator s t * 2 ^ 13 := by
    rw [isSatisfied_def] at hw; exact of_decide_eq_true hw
  have hmono : thresholdNumerator s t ≤ thresholdNumerator s' t :=
    polyNumerator_monotone (stakeQuantum s t) (stakeQuantum s' t)
      (stakeQuantum_monotone s s' t hs) (stakeQuantum_le s' t hs' ht)
  have h13 : (0:Int) ≤ 2 ^ 13 := by norm_num
  rw [isSatisfied_def]
  exact decide_eq_true (le_trans hw' (Int.mul_le_mul_of_nonneg_right hmono h13))

/-! ## §5 — TEETH: the stake cliff, and what leader election needs that a light client lacks. -/

/-- Zero stake gives a zero bound. -/
theorem zero_stake_zero_threshold (t : Nat) : thresholdNumerator 0 t = 0 := by
  simp [thresholdNumerator, stakeQuantum, polyNumerator]

/-- **THE QUANTISATION CLIFF.** The stake fraction is floored to `per_term_precision = 20` bits
BEFORE the series is evaluated (`consensus_vrf.ml:330-338`). Any delegator holding less than
`total_stake / 2^20` therefore gets `input = 0`, hence a threshold of exactly `0`, hence wins a
slot only on a VRF output of exactly `0` — one value out of `2^253`. This is an ARITHMETIC
EXCLUSION, not a small probability: such a stake is not merely unlikely to win, it cannot. -/
theorem below_the_quantum_cannot_win (v s t : Nat) (h : 2 ^ perTermPrecision * s < t) :
    isSatisfied v s t = (v == 0) := by
  have h0 : stakeQuantum s t = 0 := Nat.div_eq_of_lt h
  have hp : thresholdNumerator s t = 0 := by simp [thresholdNumerator, h0, polyNumerator]
  rw [isSatisfied_def]
  show decide ((v : Int) ≤ thresholdNumerator s t * 2 ^ 13) = (v == 0)
  rw [hp]
  cases v with
  | zero => simp
  | succ k =>
      have hpos : ¬ (((k + 1 : Nat) : Int) ≤ 0 * 2 ^ 13) := by rw [Int.zero_mul]; omega
      rw [decide_eq_false hpos]
      simp

/-- Devnet's `total_currency` at block 539768, verbatim from the block
(`metatheory/fixtures/samasika-density/devnet_window_run.json`). -/
def DEVNET_TOTAL_CURRENCY : Nat := 1584313608000001000

/-- **The cliff in MINA, on the live chain.** `1510919197082` nanomina is `1510.919197082` MINA:
on devnet today, a delegation at or below that can never produce a block, and one nanomina more
can. The two `decide`s are the two sides of the cliff. -/
theorem devnet_stake_cliff :
    2 ^ perTermPrecision * 1510919197082 < DEVNET_TOTAL_CURRENCY ∧
    ¬ (2 ^ perTermPrecision * 1510919197083 < DEVNET_TOTAL_CURRENCY) := by decide +kernel

/-- Non-vacuity, both polarities: a real-sized stake DOES clear a real-sized VRF output, and a
maximal VRF output does NOT. Without this pair the theorems above could all hold of a predicate
that is constantly `false`. -/
theorem isSatisfied_discriminates :
    isSatisfied 0 (DEVNET_TOTAL_CURRENCY / 100) DEVNET_TOTAL_CURRENCY = true ∧
    isSatisfied (2 ^ 253 - 1) (DEVNET_TOTAL_CURRENCY / 100) DEVNET_TOTAL_CURRENCY = false := by
  decide +kernel

/-- The whole-stake case: with all the stake the bound is `1 − 1/4 = 3/4` of the output space, so
a delegator holding everything still loses roughly a quarter of the slots. Samasika's `f = 3/4` is
the *active slot coefficient*, and this is it. -/
theorem full_stake_is_three_quarters :
    749990 * (2:Int) ^ 240 < polyNumerator 1048576 * 10 ^ 6 ∧
    polyNumerator 1048576 * 10 ^ 6 < 750010 * (2:Int) ^ 240 := by
  refine ⟨?_, ?_⟩ <;> · simp only [polyNumerator]; norm_num

/-! ### §5.1 — What a light client would additionally need. STATED, not footnoted.

`isSatisfied` decides leader election given `(vrf_output, my_stake, total_stake)`. A light client
holding only block headers has **none of the three** in checkable form:

1. `my_stake` is `winner_account.balance` read out of the **staking epoch ledger** at
   `winner_addr`, under a checked Merkle path against `epoch_ledger.hash`
   (`proof_of_stake.ml:718-731, 765`). The header carries the ledger HASH, not the ledger. A
   client must therefore hold, or be served with, a Merkle inclusion proof for the winner's
   account in a ledger of ~6200 accounts on devnet — per block.
2. `total_stake` is `staking_epoch_data.ledger.total_currency`, which IS in the header — this one
   is free.
3. `vrf_output` in the header is `Vrf.Output.truncate producer_vrf_result`
   (`proof_of_stake.ml:2014`), the truncated 253-bit hash. Recomputing it needs the delegator's
   *secret* scalar (`eval sk m = H(m, sk·H₂(m))`, `integrated.ml:92-95`), so a verifier cannot
   recompute it at all — it can only be *proved*, and Mina proves it inside the blockchain SNARK,
   which is also where the `Threshold.Checked.is_satisfied` constraint lives
   (`proof_of_stake.ml:747-772`).

⚑ **So: leader election is NOT checkable by a light client from headers alone, and no amount of
work on this file changes that.** The honest statements are:

* A client that verifies the **Pickles proof** inherits the threshold check, because the SNARK
  already constrains it. That is the route `LightClientMina` is on, and for it this file is a
  *specification* of what the proof is asserting, not an independent check.
* A client that wants to check leader election **without** the proof needs the staking epoch
  ledger (or per-block Merkle proofs into it) AND a standalone VRF verification — and Mina has no
  standalone VRF verifier: openmina's `mina_vrf` is evaluation-only, with verification existing
  nowhere outside the SNARK.
* The **sliding density window** (sibling file `MinaSlidingWindow`) is different in kind: it is
  computable from two consecutive headers and nothing else. That asymmetry is the real scope
  result of this lane — of Samasika's two mechanisms, one is header-checkable and one is not. -/

/-- `@[export]` seam. Callers pass the truncated VRF output as a `Nat` (little-endian, 253 bits),
the winner's balance in nanomina, and the epoch ledger's `total_currency`. -/
@[export dregg_mina_vrf_threshold_satisfied]
def dregg_mina_vrf_threshold_satisfied (vrfOutput myStake totalStake : Nat) : Bool :=
  isSatisfied vrfOutput myStake totalStake

/-! ## §6 — Hygiene. -/

#assert_axioms derivedCoefficients_are_the_deployed_ones
#assert_axioms polyNumerator_monotone
#assert_axioms more_stake_never_loses
#assert_axioms below_the_quantum_cannot_win
#assert_axioms devnet_stake_cliff
#assert_axioms isSatisfied_discriminates
#assert_axioms polyNumerator_diff_bernstein

#print axioms more_stake_never_loses
#print axioms derivedCoefficients_are_the_deployed_ones

end Dregg2.Bridge.MinaVrfThreshold

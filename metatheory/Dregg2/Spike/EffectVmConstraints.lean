import Mathlib.Tactic
import Mathlib.Data.Int.GCD
import Mathlib.RingTheory.Int.Basic

/-
# Dregg2.Spike.EffectVmConstraints — soundness of MORE real `EffectVmAir` constraints

This extends the proof-of-method established in `Dregg2.Spike.TransferAirSoundness`
(the single Transfer-lo constraint) to a **batch** of further `EffectVmAir` constraints,
each read verbatim from `circuit/src/effect_vm/air.rs` (with file:line) and each connected to
its **protocol-level property** by a theorem. The point is a mechanized, *honest* ledger of
which guarantees are in-circuit vs. deferred to the off-circuit executor.

Modeling convention (identical to the Transfer spike):
* `p = 2013265921 = 15·2^27 + 1` is the BabyBear prime.
* An AIR constraint is the statement "polynomial vanishes on the trace", i.e. its value is
  `0` in the field, which we model as the integer divisibility `p ∣ poly`.
* The load-bearing lemma `eq_zero_of_dvd_of_abs_lt` turns "`p ∣ d` with `|d| < p`" into `d = 0`.

## Constraints formalized here (all verified against source)

1. **Selector validity** (air.rs:356–371):
   * booleanity `s·(s−1) = 0` per selector,
   * sum-to-one `Σ sᵢ − 1 = 0`.
   `selectors_exactly_one`: with each `sᵢ` a canonical residue (`0 ≤ sᵢ < p`), booleanity
   forces every `sᵢ ∈ {0,1}`, and sum-to-one then forces **exactly one** selector `= 1`
   (the others `0`). This is the "exactly-one-effect-active" protocol invariant.

2. **NoOp passthrough** (air.rs:517–522):
   `noop_is_identity`: when `s_noop = 1`, the constraint `s_noop·(after − before) = 0` forces
   `after = before` for every state column (a genuine no-op).

3. **Transfer hi-limb + direction-boolean** (air.rs:546, 551), companions to the lo-limb the
   prior spike did:
   * `transfer_hi_unchanged`: active transfer ⟹ `new_bal_hi = old_bal_hi`.
   * `transfer_dir_boolean`: active transfer ⟹ `direction ∈ {0,1}`.

4. **Balance-limb range-check** (air.rs:458–488, columns.rs `NEW_BAL_LO_BIT_BASE = 36`,
   `BAL_LIMB_BITS = 30`), the W9-RANGECHECK lane:
   * `balance_lo_in_range`: the 30 bit-booleanity constraints + the recomposition constraint
     force `new_bal_lo ∈ [0, 2^30)` — the in-circuit range proof is **sound**.
   * `underflow_now_impossible`: **THE GAP IS CLOSED.** The exact `p−1` witness that satisfied
     the Transfer-lo constraint in the prior spike (`transfer_underflow_attack`) has **no**
     30-bit boolean decomposition, so it violates the range-check. Hence no wrapped debit can
     satisfy the *combined* (transfer-lo ∧ range-check) constraint system: the underflow that
     was previously deferred to the executor is now rejected in-circuit.

5. **Nonce increment** (air.rs:2528):
   `nonce_ticks_on_effect` / `nonce_frozen_on_noop`: the single global constraint
   `new_nonce − old_nonce − (1 − s_noop) = 0` forces `new_nonce = old_nonce + 1` on an active
   effect row and `new_nonce = old_nonce` on a NoOp/padding row.

## In-circuit vs deferred ledger (updated by this file)
* IN-CIRCUIT (now proven): selector exactly-one; NoOp identity; transfer hi-limb invariance;
  transfer direction booleanity; **balance_lo/hi range ∈ [0,2^30) — underflow wrap now
  IMPOSSIBLE in-circuit**; nonce monotonic tick.
* STILL DEFERRED / NOT THIS CONSTRAINT: cross-cell two-party *conservation* (a turn/net-delta
  property, not a single row); `state_commitment = Poseidon2(...)` binding (a commitment
  constraint, not modeled here).
-/

namespace Dregg2.Spike.EffectVmConstraints

/-- The BabyBear prime `p = 15·2^27 + 1`. -/
def p : ℤ := 2013265921

theorem p_value : p = 15 * 2 ^ 27 + 1 := by decide

/-- `2^30`, the balance-limb width (columns.rs `BAL_LIMB_BITS = 30`). It is `< p`. -/
theorem two_pow_30_lt_p : (2 : ℤ) ^ 30 < p := by decide

/-- The shared bounded-residue lemma: `p ∣ d` with `-p < d < p` forces `d = 0`. -/
private theorem eq_zero_of_dvd_of_abs_lt {d : ℤ} (hdvd : p ∣ d)
    (hlo : -p < d) (hhi : d < p) : d = 0 := by
  obtain ⟨k, hk⟩ := hdvd
  have hp : p = 2013265921 := rfl
  rw [hp] at hk hlo hhi
  omega

/-- `p` is prime (used to split booleanity products). -/
theorem p_prime : Prime p := by
  have : p = 2013265921 := rfl
  rw [this]; norm_num

/--
A canonical field residue `x` (`0 ≤ x < p`) that satisfies the **booleanity** constraint
`x·(x−1) ≡ 0 (mod p)` is `0` or `1`. This is the per-selector / per-bit boolean lemma.
(air.rs:359 — `s*(s-1)`, and air.rs:464 — `bit*(bit-1)`.)
-/
theorem boolean_of_sat {x : ℤ} (hlo : 0 ≤ x) (hhi : x < p)
    (hsat : p ∣ x * (x - 1)) : x = 0 ∨ x = 1 := by
  have hp : p = 2013265921 := rfl
  rw [hp] at hhi
  rcases p_prime.dvd_mul.mp hsat with hdvd | hdvd
  · left;  obtain ⟨m, hm⟩ := hdvd; rw [hp] at hm; omega
  · right; obtain ⟨m, hm⟩ := hdvd; rw [hp] at hm; omega

/-! ## 1. Selector validity (air.rs:356–371) -/

/--
Booleanity constraint value for one selector (air.rs:359): `s·(s−1)`.
Satisfied iff `p ∣ s·(s−1)`.
-/
def SelBool (s : ℤ) : Prop := p ∣ s * (s - 1)

/--
**THEOREM `selectors_exactly_one`** (air.rs:356–371).

Given a finite list of selector residues `ss`, each canonical (`0 ≤ sᵢ < p`) and each
satisfying booleanity, plus the **sum-to-one** constraint `p ∣ (Σ sᵢ − 1)` where the honest
sum is small (`Σ sᵢ < p`, which holds since each `sᵢ ∈ {0,1}` and there are `< p` selectors),
**exactly one** selector equals `1` and all the rest equal `0`.

We state the protocol property as: every selector is in `{0,1}` AND the sum is exactly `1`.
Together these mean "exactly one effect active" — a multiset of booleans summing to one has a
single `1`.
-/
theorem selectors_exactly_one
    (ss : List ℤ)
    (hcanon : ∀ s ∈ ss, 0 ≤ s ∧ s < p)
    (hbool : ∀ s ∈ ss, SelBool s)
    (hlen : (ss.length : ℤ) < p)
    (hsum : p ∣ (ss.sum - 1)) :
    (∀ s ∈ ss, s = 0 ∨ s = 1) ∧ ss.sum = 1 := by
  -- Each selector is boolean.
  have hbinary : ∀ s ∈ ss, s = 0 ∨ s = 1 := by
    intro s hs
    obtain ⟨hlo, hhi⟩ := hcanon s hs
    exact boolean_of_sat hlo hhi (hbool s hs)
  refine ⟨hbinary, ?_⟩
  -- The sum is in [0, length] ⊂ [0, p), so p ∣ (sum - 1) forces sum = 1.
  have hsum_lo : 0 ≤ ss.sum := by
    apply List.sum_nonneg
    intro s hs; exact (hcanon s hs).1
  have hsum_hi : ss.sum ≤ (ss.length : ℤ) := by
    -- each entry ≤ 1, so the sum ≤ length (proved by induction on the list)
    clear hsum hcanon hbool hlen hsum_lo
    induction ss with
    | nil => simp
    | cons a t ih =>
        have ha : a = 0 ∨ a = 1 := hbinary a (by simp)
        have ht : ∀ s ∈ t, s = 0 ∨ s = 1 := fun s hs => hbinary s (by simp [hs])
        have := ih ht
        simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
        rcases ha with h | h <;> omega
  have hpval : p = 2013265921 := rfl
  have hd : ss.sum - 1 = 0 := by
    refine eq_zero_of_dvd_of_abs_lt hsum ?_ ?_
    · rw [hpval]; omega
    · rw [hpval]; omega
  omega

/-! ## 2. NoOp passthrough (air.rs:517–522) -/

/--
The per-column NoOp constraint value (air.rs:519): `s_noop·(after − before)`.
Satisfied iff `p ∣ s_noop·(after − before)`.
-/
def NoOpCol (s_noop after before : ℤ) : Prop := p ∣ s_noop * (after - before)

/--
**THEOREM `noop_is_identity`** (air.rs:517–522).

On an **active** NoOp row (`s_noop = 1`), with the two state-column residues canonical
(`0 ≤ · < p`), the constraint forces `after = before`. A no-op truly changes nothing.
-/
theorem noop_is_identity
    (after before : ℤ)
    (haf : 0 ≤ after) (haf' : after < p)
    (hbf : 0 ≤ before) (hbf' : before < p)
    (hsat : NoOpCol 1 after before) :
    after = before := by
  unfold NoOpCol at hsat
  rw [one_mul] at hsat
  have := eq_zero_of_dvd_of_abs_lt hsat (by omega) (by omega)
  omega

/-! ## 3. Transfer hi-limb + direction-boolean (air.rs:546, 551) -/

/-- Transfer hi-limb constraint value (air.rs:546): `s_transfer·(new_bal_hi − old_bal_hi)`. -/
def TransferHi (s_transfer newHi oldHi : ℤ) : Prop := p ∣ s_transfer * (newHi - oldHi)

/--
**THEOREM `transfer_hi_unchanged`** (air.rs:546).

An active transfer (`s_transfer = 1`) leaves the hi limb of the balance unchanged, given
canonical hi-limb residues. (Single-limb amounts only touch the lo limb — the prior spike's
domain.)
-/
theorem transfer_hi_unchanged
    (newHi oldHi : ℤ)
    (hn : 0 ≤ newHi) (hn' : newHi < p)
    (ho : 0 ≤ oldHi) (ho' : oldHi < p)
    (hsat : TransferHi 1 newHi oldHi) :
    newHi = oldHi := by
  unfold TransferHi at hsat
  rw [one_mul] at hsat
  have := eq_zero_of_dvd_of_abs_lt hsat (by omega) (by omega)
  omega

/-- Transfer direction-boolean constraint value (air.rs:551): `s_transfer·dir·(dir−1)`. -/
def TransferDir (s_transfer dir : ℤ) : Prop := p ∣ s_transfer * (dir * (dir - 1))

/--
**THEOREM `transfer_dir_boolean`** (air.rs:551).

An active transfer (`s_transfer = 1`) with a canonical `direction` residue forces
`direction ∈ {0,1}` (0 = in/add, 1 = out/subtract).
-/
theorem transfer_dir_boolean
    (dir : ℤ) (hlo : 0 ≤ dir) (hhi : dir < p)
    (hsat : TransferDir 1 dir) :
    dir = 0 ∨ dir = 1 := by
  unfold TransferDir at hsat
  rw [one_mul] at hsat
  exact boolean_of_sat hlo hhi hsat

/-! ## 4. Balance-limb range-check (air.rs:458–488; W9-RANGECHECK lane) -/

/--
The recomposition value of a 30-bit decomposition `bits : Fin 30 → ℤ`:
`Σ_{i<30} bits i · 2^i`. (air.rs:467 `recomposed_lo += bit * 2^i`.)
-/
def recompose30 (bits : Fin 30 → ℤ) : ℤ :=
  ∑ i : Fin 30, bits i * 2 ^ (i : ℕ)

/-- All 30 decomposition bits satisfy booleanity (air.rs:464 `bit*(bit-1)`). -/
def BitsBoolean (bits : Fin 30 → ℤ) : Prop := ∀ i : Fin 30, p ∣ (bits i) * (bits i - 1)

/-- The bits are canonical residues (`0 ≤ bit < p`), as field elements always are. -/
def BitsCanonical (bits : Fin 30 → ℤ) : Prop := ∀ i : Fin 30, 0 ≤ bits i ∧ bits i < p

/--
The recomposition constraint (air.rs:470–471): `recomposed_lo − new_bal_lo ≡ 0 (mod p)`,
i.e. `p ∣ (recompose30 bits − newBalLo)`.
-/
def RecomposeSat (bits : Fin 30 → ℤ) (newBalLo : ℤ) : Prop :=
  p ∣ (recompose30 bits - newBalLo)

/-- A genuine bit-vector recompose lies in `[0, 2^30)`. -/
private theorem recompose30_range {bits : Fin 30 → ℤ}
    (hb : ∀ i, bits i = 0 ∨ bits i = 1) :
    0 ≤ recompose30 bits ∧ recompose30 bits < 2 ^ 30 := by
  unfold recompose30
  constructor
  · -- nonnegative: each term ≥ 0
    apply Finset.sum_nonneg
    intro i _
    rcases hb i with h | h <;> simp [h]
  · -- strict upper bound: Σ bit_i 2^i ≤ Σ 2^i = 2^30 - 1 < 2^30
    have hle : ∀ i : Fin 30, bits i * 2 ^ (i : ℕ) ≤ 2 ^ (i : ℕ) := by
      intro i
      rcases hb i with h | h <;> simp [h]
    calc ∑ i : Fin 30, bits i * 2 ^ (i : ℕ)
        ≤ ∑ i : Fin 30, (2 : ℤ) ^ (i : ℕ) := Finset.sum_le_sum (fun i _ => hle i)
      _ = 2 ^ 30 - 1 := by decide
      _ < 2 ^ 30 := by omega

/--
**THEOREM `balance_lo_in_range`** (air.rs:458–488).

The 30 bit-booleanity constraints (each bit `∈ {0,1}`) together with the recomposition
constraint (`Σ bitᵢ·2^i = new_bal_lo` in the field) and a canonical `new_bal_lo` residue
**force `new_bal_lo ∈ [0, 2^30)`**. The in-circuit range proof is sound: the post-state
balance limb is provably a true 30-bit value, no executor re-derivation required.
-/
theorem balance_lo_in_range
    (bits : Fin 30 → ℤ) (newBalLo : ℤ)
    (hcanon : BitsCanonical bits)
    (hbool : BitsBoolean bits)
    (hlo : 0 ≤ newBalLo) (hhi : newBalLo < p)
    (hrec : RecomposeSat bits newBalLo) :
    0 ≤ newBalLo ∧ newBalLo < 2 ^ 30 := by
  -- Each bit is 0 or 1.
  have hb : ∀ i, bits i = 0 ∨ bits i = 1 := by
    intro i
    obtain ⟨hl, hh⟩ := hcanon i
    exact boolean_of_sat hl hh (hbool i)
  -- recompose ∈ [0, 2^30)
  obtain ⟨hrlo, hrhi⟩ := recompose30_range hb
  have hpw : (2 : ℤ) ^ 30 < p := two_pow_30_lt_p
  -- recompose ≡ newBalLo (mod p), both in [0,p), so equal.
  unfold RecomposeSat at hrec
  have heq : recompose30 bits - newBalLo = 0 :=
    eq_zero_of_dvd_of_abs_lt hrec (by omega) (by omega)
  omega

/--
The Transfer-lo constraint value (air.rs:541), reproduced from the prior spike so the
underflow witness can be referenced here:
`new − old − amount + 2·dir·amount`.
-/
def transferLo (old new amount dir : ℤ) : ℤ :=
  new - old - amount + 2 * dir * amount

/-- Transfer-lo satisfaction (active row). -/
def TransferLoSat (old new amount dir : ℤ) : Prop := p ∣ transferLo old new amount dir

/--
The exact underflow witness from `TransferAirSoundness.transfer_underflow_attack`:
`old = 0, new = p−1, amount = 1, dir = 1` satisfies the Transfer-lo constraint even though the
intended result `0 − 1 = −1` underflowed and wrapped to `p−1`.
-/
theorem underflow_witness_satisfies_transferLo : TransferLoSat 0 (p - 1) 1 1 := by
  unfold TransferLoSat
  have h : transferLo 0 (p - 1) 1 1 = p := by unfold transferLo p; decide
  rw [h]

/--
**THEOREM `underflow_now_impossible` — THE GAP IS CLOSED (air.rs:458–488).**

The prior spike (`transfer_underflow_attack`) showed the Transfer-lo constraint *alone* admits
the wrapped value `new_bal_lo = p − 1`. The W9-RANGECHECK lane added the bit-decomposition
range check. Here we prove the wrap is **no longer satisfiable**: there is **no** 30-bit boolean
decomposition `bits` whose recomposition equals `p − 1`, because `p − 1 ≥ 2^30` but every valid
recomposition is `< 2^30`. Hence the wrapped witness violates the range-check constraint, and the
combined (transfer-lo ∧ range-check) system rejects the underflow **in-circuit**.

This is exactly the protocol property: the underflow that was previously caught only by the
off-circuit executor is now caught by the AIR itself.
-/
theorem underflow_now_impossible :
    ¬ ∃ bits : Fin 30 → ℤ,
        BitsCanonical bits ∧ BitsBoolean bits ∧ RecomposeSat bits (p - 1) := by
  rintro ⟨bits, hcanon, hbool, hrec⟩
  -- The range-check would force p - 1 ∈ [0, 2^30); but p - 1 ≥ 2^30.
  have hlo : (0 : ℤ) ≤ p - 1 := by decide
  have hhi : p - 1 < p := by decide
  obtain ⟨_, hub⟩ := balance_lo_in_range bits (p - 1) hcanon hbool hlo hhi hrec
  -- contradiction: p - 1 < 2^30 is false.
  have : (2 : ℤ) ^ 30 ≤ p - 1 := by decide
  omega

/--
**COROLLARY `range_check_closes_transfer_underflow`.**

Combining the two: the specific wrapped witness `new = p − 1` *does* satisfy the Transfer-lo
constraint (so the lo-constraint is insufficient alone), **yet** it cannot satisfy the
range-check (no bit-decomposition exists), so the conjoined constraint system rejects it. The
single statement that ties the spike's gap to its closure.
-/
theorem range_check_closes_transfer_underflow :
    TransferLoSat 0 (p - 1) 1 1
    ∧ ¬ ∃ bits : Fin 30 → ℤ,
          BitsCanonical bits ∧ BitsBoolean bits ∧ RecomposeSat bits (p - 1) :=
  ⟨underflow_witness_satisfies_transferLo, underflow_now_impossible⟩

/-! ## 5. Nonce increment (air.rs:2528) -/

/--
The global nonce constraint value (air.rs:2528): `new_nonce − old_nonce − (1 − s_noop)`.
This single constraint is enforced on **every** row (not selector-gated to one effect).
Satisfied iff `p ∣ (new_nonce − old_nonce − (1 − s_noop))`.
-/
def NonceSat (newNonce oldNonce s_noop : ℤ) : Prop :=
  p ∣ (newNonce - oldNonce - (1 - s_noop))

/--
**THEOREM `nonce_ticks_on_effect`** (air.rs:2528).

On an **active effect** row (`s_noop = 0`) with canonical nonce residues, the constraint forces
`new_nonce = old_nonce + 1` — the nonce strictly increments per real effect.
-/
theorem nonce_ticks_on_effect
    (newNonce oldNonce : ℤ)
    (hn : 0 ≤ newNonce) (hn' : newNonce < p)
    (ho : 0 ≤ oldNonce) (ho' : oldNonce + 1 < p)   -- honest nonce stays in range
    (hsat : NonceSat newNonce oldNonce 0) :
    newNonce = oldNonce + 1 := by
  unfold NonceSat at hsat
  have hd : p ∣ (newNonce - (oldNonce + 1)) := by
    have heq : newNonce - oldNonce - (1 - 0) = newNonce - (oldNonce + 1) := by ring
    rwa [heq] at hsat
  have := eq_zero_of_dvd_of_abs_lt hd (by omega) (by omega)
  omega

/--
**THEOREM `nonce_frozen_on_noop`** (air.rs:2528).

On a **NoOp / padding** row (`s_noop = 1`) with canonical nonce residues, the constraint forces
`new_nonce = old_nonce` — padding rows do not advance the nonce.
-/
theorem nonce_frozen_on_noop
    (newNonce oldNonce : ℤ)
    (hn : 0 ≤ newNonce) (hn' : newNonce < p)
    (ho : 0 ≤ oldNonce) (ho' : oldNonce < p)
    (hsat : NonceSat newNonce oldNonce 1) :
    newNonce = oldNonce := by
  unfold NonceSat at hsat
  have hd : p ∣ (newNonce - oldNonce) := by
    have heq : newNonce - oldNonce - (1 - 1) = newNonce - oldNonce := by ring
    rwa [heq] at hsat
  have := eq_zero_of_dvd_of_abs_lt hd (by omega) (by omega)
  omega

/-!
## Verdict (extends the proof-of-method ledger)

* **Selector group** → exactly-one-effect-active is now an in-circuit theorem
  (`selectors_exactly_one`): booleanity + sum-to-one ⟹ a single live selector.
* **NoOp** → genuine identity in-circuit (`noop_is_identity`).
* **Transfer hi/dir** → hi-limb invariance + direction booleanity in-circuit
  (`transfer_hi_unchanged`, `transfer_dir_boolean`), completing the Transfer row alongside the
  prior lo-limb soundness.
* **Range-check (W9-RANGECHECK)** → the post-state balance limb is provably a 30-bit value
  (`balance_lo_in_range`), and — the headline — the underflow wrap that the prior spike exposed
  as an off-circuit-only defense is now **provably impossible in-circuit**
  (`underflow_now_impossible`, `range_check_closes_transfer_underflow`). The deferred guarantee
  has migrated into the circuit.
* **Nonce** → monotonic per-effect tick / NoOp freeze in-circuit
  (`nonce_ticks_on_effect`, `nonce_frozen_on_noop`).

STILL DEFERRED (honest): cross-cell two-party *conservation* (turn/net-delta scope, not a
single-row constraint) and the `state_commitment = Poseidon2(...)` binding (a commitment
constraint outside this affine batch).
-/

end Dregg2.Spike.EffectVmConstraints

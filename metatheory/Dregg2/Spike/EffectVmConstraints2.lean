import Mathlib.Tactic
import Mathlib.Data.Int.GCD
import Mathlib.RingTheory.Int.Basic

/-
# Dregg2.Spike.EffectVmConstraints2 — soundness of yet MORE real `EffectVmAir` constraints

A sibling to `Dregg2.Spike.EffectVmConstraints`, continuing the *honest* ledger of which
`EffectVmAir` guarantees are in-circuit vs. deferred. Every constraint below is read verbatim
from `circuit/src/effect_vm/air.rs` (cited with file:line) and connected to its protocol-level
property by a theorem. We reuse the exact modeling discipline of the prior spikes:

Modeling convention (identical to the Transfer/EffectVmConstraints spikes):
* `p = 2013265921 = 15·2^27 + 1` is the BabyBear prime.
* An AIR constraint is "the polynomial vanishes on the trace", i.e. its value is `0` in the
  field, modeled as integer divisibility `p ∣ poly` over `ℤ`.
* `eq_zero_of_dvd_of_abs_lt` turns "`p ∣ d` with `|d| < p`" into `d = 0`.

## Constraints formalized here (all verified against source)

1. **SetField per-field gating + sum** (air.rs:602–638, `BAL_LIMB_BITS`/`FIELD_BASE` in
   columns.rs:285, 322):
   * per-field gate (air.rs:606): `s_setfield · (field_index − j) · (new_fⱼ − old_fⱼ)` for
     each `j ∈ 0..8`. For `j ≠ field_index` (with `field_index ∈ {0..7}`) the factor
     `(field_index − j)` is a nonzero field element, so the constraint forces
     `new_fⱼ = old_fⱼ` — **non-target fields are frozen**.
   * sum (air.rs:636): `s_setfield · (Σⱼ (new_fⱼ − old_fⱼ) − (new_value − old_value_at_idx))`
     where `old_value_at_idx = aux[0]`. Combined with the per-field freezing, this pins the
     **single** target field's new value to `old_value_at_idx + (new_value − old_value_at_idx)`.
   * `setfield_targets_exactly_one_field`: constraint satisfied ⟹ exactly the targeted field
     changed (to a determined value), all others fixed.
   * `setfield_aux_honesty_gap`: **THE GAP.** The new target value equals `new_value` **only
     if** the prover sets `aux[0] = old_value_at_idx` to the *true* old field value. That aux
     honesty is NOT pinned by these two constraints (`aux[0]` is a free witness column). A
     dishonest `aux[0]` lets the target field land at the wrong value while still satisfying
     both constraints. (air.rs:629 — `old_value_at_idx = local[AUX_BASE + 0]`, a witness.)

2. **balance_hi 30-bit range-check** (air.rs:475–487, `NEW_BAL_HI_BIT_BASE = 66`,
   `BAL_LIMB_BITS = 30`): the twin of the lo-limb check the prior spike proved. The 30
   bit-booleanity constraints + the recomposition constraint force `new_bal_hi ∈ [0, 2^30)`.
   `balance_hi_in_range`: in-circuit range proof for the hi limb is sound.
   HONESTY: the lane width is **30 bits, not 34** — `BAL_LIMB_BITS = 30` (columns.rs:322).
   30 is chosen so `2^30 < p`, which is exactly what makes the in-field recomposition unique
   and non-wrapping. A 34-bit lane would have `2^34 > p` and the recomposition could wrap,
   defeating the range proof. So 30 is the *sound* choice, and we prove the bound `2^30`.

3. **state_commitment = Poseidon2(…) boundary binding SHAPE** (air.rs:2532–2595 transition,
   air.rs:2695–2711 boundary): the §8 hash primitive is treated as an **opaque** function
   `H : List F → F` (we cannot and do not formalize Poseidon2's algebra — PORTAL-OK). We state
   the real constraint shape (a 4-leaf hash tree: `inter1/2/3` then root) and the two boundary
   pins (row-0 `state_before.commit = OLD_COMMIT`, last-row `state_after.commit = NEW_COMMIT`).
   ⚑ The binding CONSEQUENCE is NOT stated here any more: `state_commitment_binds_state` and
   `state_commitment_no_silent_change` were conditioned on the refuted `CommitTreeInjective` and
   are DELETED (2026-08-01, see the tombstone at the `CommitTreeInjective` site). The PI-binds-
   the-post-state claim lives, DISCHARGED, as `CommitTreeRegrounded.state_commitment_binds_state_rom`
   / `state_commitment_no_silent_change_rom` — negligible advantage for every query-bounded
   equivocator over the PROVED keyed-ROM floor, not a Boolean uniqueness.

## In-circuit vs deferred ledger (updated by this file)
* IN-CIRCUIT (now proven): SetField freezes non-target fields and pins the target field's
  delta (`setfield_targets_exactly_one_field`); balance_hi limb ∈ [0,2^30)
  (`balance_hi_in_range`). The state_commitment shape (`commitTree`, `StateCommitSat`) is stated
  here; its BINDING is carried by `CommitTreeRegrounded`'s ROM bounds, not by this file.
* STILL DEFERRED / GAP EXPOSED: SetField target-value *correctness* depends on the
  off-circuit honesty of the `aux[0]` old-value witness (`setfield_aux_honesty_gap`); the
  collision-resistance of Poseidon2 itself is a §8 portal assumption, not an in-circuit fact.
-/

namespace Dregg2.Spike.EffectVmConstraints2

/-- The BabyBear prime `p = 15·2^27 + 1`. -/
def p : ℤ := 2013265921

theorem p_value : p = 15 * 2 ^ 27 + 1 := by decide

/-- `2^30`, the balance-limb width (columns.rs:322 `BAL_LIMB_BITS = 30`). It is `< p`. -/
theorem two_pow_30_lt_p : (2 : ℤ) ^ 30 < p := by decide

/-- The shared bounded-residue lemma: `p ∣ d` with `-p < d < p` forces `d = 0`. -/
private theorem eq_zero_of_dvd_of_abs_lt {d : ℤ} (hdvd : p ∣ d)
    (hlo : -p < d) (hhi : d < p) : d = 0 := by
  obtain ⟨k, hk⟩ := hdvd
  have hp : p = 2013265921 := rfl
  rw [hp] at hk hlo hhi
  omega

set_option maxRecDepth 8192 in
/-- `p` is prime (used to split booleanity products). -/
theorem p_prime : Prime p := by
  have : p = 2013265921 := rfl
  rw [this]; norm_num

/-- A canonical residue satisfying booleanity `p ∣ x·(x−1)` is `0` or `1`. -/
theorem boolean_of_sat {x : ℤ} (hlo : 0 ≤ x) (hhi : x < p)
    (hsat : p ∣ x * (x - 1)) : x = 0 ∨ x = 1 := by
  have hp : p = 2013265921 := rfl
  rw [hp] at hhi
  rcases p_prime.dvd_mul.mp hsat with hdvd | hdvd
  · left;  obtain ⟨m, hm⟩ := hdvd; rw [hp] at hm; omega
  · right; obtain ⟨m, hm⟩ := hdvd; rw [hp] at hm; omega

/-! ## 1. SetField per-field gating + sum (air.rs:602–638) -/

/--
The per-field gate constraint value for field slot `j` (air.rs:606):
`s_setfield · (field_index − j) · (new_fⱼ − old_fⱼ)`.
On an active SetField row (`s_setfield = 1`) this is `(field_index − j)·(new_fⱼ − old_fⱼ)`.
-/
def SetFieldGate (sSet fieldIdx j newFj oldFj : ℤ) : Prop :=
  p ∣ sSet * ((fieldIdx - j) * (newFj - oldFj))

/--
The SetField sum constraint value (air.rs:636):
`s_setfield · (Σⱼ (new_fⱼ − old_fⱼ) − (new_value − old_value_at_idx))`.
-/
def SetFieldSum (sSet diffSum newValue oldValAtIdx : ℤ) : Prop :=
  p ∣ sSet * (diffSum - (newValue - oldValAtIdx))

/--
**Non-target freeze lemma** (air.rs:606). On an active SetField row, for a field slot `j`
distinct from `field_index` (both canonical small indices in `{0..7}`, so their difference is a
nonzero residue with `|field_index − j| < p`), with canonical field residues, the gate
constraint forces `new_fⱼ = old_fⱼ`.
-/
theorem setfield_nontarget_frozen
    (fieldIdx j newFj oldFj : ℤ)
    (hfi : 0 ≤ fieldIdx) (hfi' : fieldIdx ≤ 7)
    (hj : 0 ≤ j) (hj' : j ≤ 7)
    (hne : fieldIdx ≠ j)
    (hnf : 0 ≤ newFj) (hnf' : newFj < p)
    (hof : 0 ≤ oldFj) (hof' : oldFj < p)
    (hsat : SetFieldGate 1 fieldIdx j newFj oldFj) :
    newFj = oldFj := by
  unfold SetFieldGate at hsat
  rw [one_mul] at hsat
  -- p prime; p ∣ (fieldIdx - j)·(newFj - oldFj). The first factor has |·| ≤ 7 < p and is
  -- nonzero, so p does not divide it; hence p ∣ (newFj - oldFj), forcing equality.
  rcases p_prime.dvd_mul.mp hsat with hdvd | hdvd
  · -- p ∣ (fieldIdx - j) is impossible: 0 < |fieldIdx - j| ≤ 7 < p.
    exfalso
    obtain ⟨m, hm⟩ := hdvd
    have hp : p = 2013265921 := rfl
    rw [hp] at hm
    omega
  · have := eq_zero_of_dvd_of_abs_lt hdvd (by omega) (by omega)
    omega

/--
**THEOREM `setfield_targets_exactly_one_field`** (air.rs:602–638).

An active SetField row (`s_setfield = 1`) with a canonical target index `field_index ∈ {0..7}`,
canonical field residues, all eight per-field gate constraints satisfied, and the sum constraint
satisfied, forces:
* every non-target field `j ≠ field_index` is unchanged (`new_fⱼ = old_fⱼ`); and
* the targeted field's change is exactly `new_value − old_value_at_idx`, i.e.
  `new_f[field_index] = old_f[field_index] + (new_value − old_value_at_idx)`.

We model the eight slots as functions `oldF newF : Fin 8 → ℤ` and identify the target slot by an
index `t : Fin 8` with `field_index = (t : ℤ)`. "Exactly one field changed" is captured by:
all `j ≠ t` are frozen, and the total `Σ(newF − oldF)` is pinned, which (given the freezing)
equals the single target delta.
-/
theorem setfield_targets_exactly_one_field
    (oldF newF : Fin 8 → ℤ) (t : Fin 8) (newValue oldValAtIdx : ℤ)
    (hcanon : ∀ j : Fin 8, (0 ≤ oldF j ∧ oldF j < p) ∧ (0 ≤ newF j ∧ newF j < p))
    (hgate : ∀ j : Fin 8, SetFieldGate 1 (t : ℤ) (j : ℤ) (newF j) (oldF j))
    (hsum : SetFieldSum 1 (∑ j : Fin 8, (newF j - oldF j)) newValue oldValAtIdx) :
    (∀ j : Fin 8, j ≠ t → newF j = oldF j)
    ∧ p ∣ ((newF t - oldF t) - (newValue - oldValAtIdx)) := by
  -- Step 1: every non-target field is frozen.
  have hfrozen : ∀ j : Fin 8, j ≠ t → newF j = oldF j := by
    intro j hjt
    have hti : (0 : ℤ) ≤ (t : ℤ) ∧ (t : ℤ) ≤ 7 := by
      refine ⟨by positivity, ?_⟩
      have : (t : ℕ) ≤ 7 := by omega
      exact_mod_cast this
    have hji : (0 : ℤ) ≤ (j : ℤ) ∧ (j : ℤ) ≤ 7 := by
      refine ⟨by positivity, ?_⟩
      have : (j : ℕ) ≤ 7 := by omega
      exact_mod_cast this
    have hne : (t : ℤ) ≠ (j : ℤ) := by
      intro h
      apply hjt
      have : (t : ℕ) = (j : ℕ) := by exact_mod_cast h
      exact (Fin.ext this).symm
    obtain ⟨⟨ho, ho'⟩, hn, hn'⟩ := hcanon j
    exact setfield_nontarget_frozen (t : ℤ) (j : ℤ) (newF j) (oldF j)
      hti.1 hti.2 hji.1 hji.2 hne hn hn' ho ho' (hgate j)
  refine ⟨hfrozen, ?_⟩
  -- Step 2: the sum collapses to the single target delta (every other term is 0).
  have hsum_collapse : (∑ j : Fin 8, (newF j - oldF j)) = newF t - oldF t := by
    rw [Finset.sum_eq_single t]
    · intro b _ hbt
      rw [hfrozen b hbt]; ring
    · intro h; exact absurd (Finset.mem_univ t) h
  -- Step 3: the sum constraint, after collapse, is exactly the target-delta divisibility.
  -- We stop at the FIELD-LEVEL guarantee (a congruence mod p), which is precisely what the AIR
  -- constraint enforces: the circuit pins the residue, not an unbounded integer. Upgrading to
  -- an integer equation needs a magnitude bound on `newValue − oldValAtIdx` (the dedicated
  -- corollary below adds it).
  unfold SetFieldSum at hsum
  rw [one_mul, hsum_collapse] at hsum
  exact hsum

/--
**COROLLARY `setfield_target_value_pinned`** (air.rs:602–638).

Under the additional *honest range* hypotheses that the targeted intended delta
`newValue − oldValAtIdx` is small enough that the combined target difference stays in `(−p, p)`
(`-p < (newF t - oldF t) - (newValue - oldValAtIdx) < p`), the field-level congruence sharpens
to the exact integer equation: the targeted field becomes `oldF t + (newValue − oldValAtIdx)`.
-/
theorem setfield_target_value_pinned
    (oldF newF : Fin 8 → ℤ) (t : Fin 8) (newValue oldValAtIdx : ℤ)
    (hcanon : ∀ j : Fin 8, (0 ≤ oldF j ∧ oldF j < p) ∧ (0 ≤ newF j ∧ newF j < p))
    (hgate : ∀ j : Fin 8, SetFieldGate 1 (t : ℤ) (j : ℤ) (newF j) (oldF j))
    (hsum : SetFieldSum 1 (∑ j : Fin 8, (newF j - oldF j)) newValue oldValAtIdx)
    (hlo : -p < (newF t - oldF t) - (newValue - oldValAtIdx))
    (hhi : (newF t - oldF t) - (newValue - oldValAtIdx) < p) :
    (∀ j : Fin 8, j ≠ t → newF j = oldF j)
    ∧ newF t = oldF t + (newValue - oldValAtIdx) := by
  obtain ⟨hfrozen, hdvd⟩ :=
    setfield_targets_exactly_one_field oldF newF t newValue oldValAtIdx hcanon hgate hsum
  refine ⟨hfrozen, ?_⟩
  have := eq_zero_of_dvd_of_abs_lt hdvd hlo hhi
  omega

/--
**THEOREM `setfield_aux_honesty_gap` — THE GAP (air.rs:629), formalized.**

The target field is pinned to `oldF t + (newValue − oldValAtIdx)` where `oldValAtIdx = aux[0]`
is a **free witness column** (air.rs:629). The constraints do NOT bind `aux[0]` to the true old
value `oldF t`. So a dishonest prover can pick `aux[0] = oldValAtIdx ≠ oldF t` and the target
field lands at `oldF t + (newValue − oldValAtIdx) ≠ newValue` while STILL satisfying both the
gate constraints (non-target fields frozen) and the sum constraint.

Concretely (a witnessable counterexample over the integers): take field slot `t = 0`, all old
fields `0`, intended `newValue = 5`, but a lying `aux[0] = oldValAtIdx = 3`. Set
`newF 0 = 0 + (5 − 3) = 2` and all other `newF j = 0`. Every gate constraint holds (non-targets
frozen) and the sum constraint holds (`Σ delta = 2 = 5 − 3`), yet the field became `2`, not the
intended `5`. The intended-value correctness is therefore NOT in-circuit; it rests on the
off-circuit executor / witness generator setting `aux[0]` to the genuine old field value.
-/
theorem setfield_aux_honesty_gap :
    ∃ (oldF newF : Fin 8 → ℤ) (t : Fin 8) (newValue oldValAtIdx : ℤ),
        (∀ j : Fin 8, SetFieldGate 1 (t : ℤ) (j : ℤ) (newF j) (oldF j))
        ∧ SetFieldSum 1 (∑ j : Fin 8, (newF j - oldF j)) newValue oldValAtIdx
        ∧ oldValAtIdx ≠ oldF t          -- the aux column LIES about the old value
        ∧ newF t ≠ newValue := by        -- so the field lands at the WRONG value
  -- old fields all 0; target slot 0; newF 0 = 2, rest 0; newValue = 5, lying aux[0] = 3.
  refine ⟨fun _ => 0, fun j => if j = 0 then 2 else 0, 0, 5, 3, ?_, ?_, ?_, ?_⟩
  · -- every gate constraint holds: factor (0 - j)·(newFj - 0). For j = 0 first factor is 0;
    -- for j ≠ 0 the field is unchanged (newFj = 0). So the product is 0, divisible by p.
    intro j
    unfold SetFieldGate
    by_cases hj : j = 0
    · subst hj; simp
    · simp [hj]
  · -- sum constraint: Σ delta = 2 (only slot 0 changed), and 5 - 3 = 2. So value is 0.
    unfold SetFieldSum
    have hsum : (∑ j : Fin 8, ((if j = 0 then (2:ℤ) else 0) - 0)) = 2 := by decide
    rw [hsum]; simp
  · -- oldValAtIdx = 3 ≠ oldF 0 = 0.
    norm_num
  · -- newF 0 = 2 ≠ newValue = 5.
    norm_num

/-! ## 2. balance_hi 30-bit range-check (air.rs:475–487; `NEW_BAL_HI_BIT_BASE = 66`) -/

/--
The recomposition value of a 30-bit hi-limb decomposition (air.rs:482
`recomposed_hi += bit * 2^i`).
-/
def recompose30 (bits : Fin 30 → ℤ) : ℤ :=
  ∑ i : Fin 30, bits i * 2 ^ (i : ℕ)

/-- All 30 hi-limb bits satisfy booleanity (air.rs:479 `bit*(bit-1)`). -/
def BitsBoolean (bits : Fin 30 → ℤ) : Prop := ∀ i : Fin 30, p ∣ (bits i) * (bits i - 1)

/-- The bits are canonical residues (`0 ≤ bit < p`). -/
def BitsCanonical (bits : Fin 30 → ℤ) : Prop := ∀ i : Fin 30, 0 ≤ bits i ∧ bits i < p

/-- The hi recomposition constraint (air.rs:484–485): `recomposed_hi − new_bal_hi ≡ 0 (mod p)`. -/
def RecomposeHiSat (bits : Fin 30 → ℤ) (newBalHi : ℤ) : Prop :=
  p ∣ (recompose30 bits - newBalHi)

/-- A genuine bit-vector recompose lies in `[0, 2^30)`. -/
private theorem recompose30_range {bits : Fin 30 → ℤ}
    (hb : ∀ i, bits i = 0 ∨ bits i = 1) :
    0 ≤ recompose30 bits ∧ recompose30 bits < 2 ^ 30 := by
  unfold recompose30
  constructor
  · apply Finset.sum_nonneg
    intro i _
    rcases hb i with h | h <;> simp [h]
  · have hle : ∀ i : Fin 30, bits i * 2 ^ (i : ℕ) ≤ 2 ^ (i : ℕ) := by
      intro i
      rcases hb i with h | h <;> simp [h]
    calc ∑ i : Fin 30, bits i * 2 ^ (i : ℕ)
        ≤ ∑ i : Fin 30, (2 : ℤ) ^ (i : ℕ) := Finset.sum_le_sum (fun i _ => hle i)
      _ = 2 ^ 30 - 1 := by decide
      _ < 2 ^ 30 := by omega

/--
**THEOREM `balance_hi_in_range`** (air.rs:475–487) — the twin of `balance_lo_in_range`.

The 30 hi-limb bit-booleanity constraints plus the hi recomposition constraint, with a canonical
`new_bal_hi` residue, force `new_bal_hi ∈ [0, 2^30)`. The in-circuit range proof for the HIGH
balance limb is sound, identically to the low limb.

HONESTY: the lane is 30 bits (`BAL_LIMB_BITS = 30`, columns.rs:322), **not 34**. 30 is the
soundness-mandated width: `2^30 < p` (`two_pow_30_lt_p`) makes the in-field recomposition unique
and non-wrapping. A 34-bit lane would have `2^34 > p`, so the recomposition could wrap and the
range proof would NOT pin a true sub-`2^34` value.
-/
theorem balance_hi_in_range
    (bits : Fin 30 → ℤ) (newBalHi : ℤ)
    (hcanon : BitsCanonical bits)
    (hbool : BitsBoolean bits)
    (hlo : 0 ≤ newBalHi) (hhi : newBalHi < p)
    (hrec : RecomposeHiSat bits newBalHi) :
    0 ≤ newBalHi ∧ newBalHi < 2 ^ 30 := by
  have hb : ∀ i, bits i = 0 ∨ bits i = 1 := by
    intro i
    obtain ⟨hl, hh⟩ := hcanon i
    exact boolean_of_sat hl hh (hbool i)
  obtain ⟨hrlo, hrhi⟩ := recompose30_range hb
  have hpw : (2 : ℤ) ^ 30 < p := two_pow_30_lt_p
  unfold RecomposeHiSat at hrec
  have heq : recompose30 bits - newBalHi = 0 :=
    eq_zero_of_dvd_of_abs_lt hrec (by omega) (by omega)
  omega

/-! ## 3. state_commitment = Poseidon2(…) boundary binding SHAPE (air.rs:2532–2595, 2695–2711) -/

/--
The §8 hash primitive, treated as an **opaque function** `H : List ℤ → ℤ`. We do NOT formalize
Poseidon2's algebra (that is the §8 hash-primitive portal). It is a parameter to the binding
statement, exactly as the circuit calls `hash_4_to_1` as a black box. (air.rs:6 import.)
-/
abbrev Hash := List ℤ → ℤ

/--
The four-leaf state-commitment hash tree (air.rs:2540–2543, 2557–2592), as a function of the
post-state tuple and an opaque hash `H`:
```
inter1 = H[bal_lo, bal_hi, nonce, field0]
inter2 = H[field1, field2, field3, field4]
inter3 = H[field5, field6, field7, cap_root]
root   = H[inter1, inter2, inter3, 0]
```
We package the post-state tuple as a single `List ℤ` of the 12 committed columns in the exact
order the circuit hashes them.
-/
def commitTree (H : Hash) (st : List ℤ) : ℤ :=
  match st with
  | [balLo, balHi, nonce, f0, f1, f2, f3, f4, f5, f6, f7, capRoot] =>
      let inter1 := H [balLo, balHi, nonce, f0]
      let inter2 := H [f1, f2, f3, f4]
      let inter3 := H [f5, f6, f7, capRoot]
      H [inter1, inter2, inter3, 0]
  | _ => 0  -- malformed tuple (not 12 columns) is out of scope of the shape

/--
The transition constraint of group 4 (air.rs:2546–2594): a satisfying trace has its
`state_after.STATE_COMMIT` column equal to `commitTree H state_after`. Modeled as the equation
the AIR pins (the intermediate aux columns are existentially the honest `H` outputs).
-/
def StateCommitSat (H : Hash) (st : List ℤ) (commit : ℤ) : Prop :=
  commit = commitTree H st

/-- The load-bearing §8-portal hypothesis: `commitTree H` is injective on the committed tuples
    (a direct consequence of Poseidon2 collision-resistance). This is an **honest carried Prop
    (PORTAL-OK)** — supplied as a hypothesis, never proved here.

⚠ **BROKEN AS NAMED — FALSE at deployed parameters, so `state_commitment_binds_state` and
`state_commitment_no_silent_change` below are VACUOUSLY TRUE there**
(`Spike.CommitTreeRegrounded.commitTreeInjective_false_babyBear`; `docs/deos/VACUITY-SWEEP.md`
FINDING 2). It is injectivity on the INFINITE `List ℤ` while the root is ONE felt. ⚠ "PORTAL-OK,
carried as a hypothesis, never proved here" is NOT the protection it reads as: a hypothesis that is
FALSE at deployed parameters makes its consumers vacuous, and `#assert_axioms` cannot see it — being
carried honestly is not the same as being satisfiable.

**The honest replacement is `Spike.CommitTreeRegrounded`** — `state_commitment_binds_state`'s
advantage-bounded sibling, from a REAL state-equivocation game (the adversary exhibits two DISTINCT
post-state tuples behind ONE published `NEW_COMMIT`) via a REAL reduction, carrying an explicit
undischarged `Eff`. This def is KEPT so the record and the teeth keep compiling. -/
def CommitTreeInjective (H : Hash) : Prop :=
  ∀ a b : List ℤ, commitTree H a = commitTree H b → a = b

/-! ## ⚑ DELETED (2026-08-01) — `state_commitment_binds_state`, `state_commitment_no_silent_change`

**What they claimed.** `state_commitment_binds_state` (air.rs:2532–2595 transition + air.rs:2707–2711
last-row boundary): two traces whose `state_after.STATE_COMMIT` satisfies the group-4 transition and
is boundary-pinned to the SAME public input `NEW_COMMIT` commit to the same 12-column post-state
tuple. `state_commitment_no_silent_change` (air.rs:2546–2594) was its corollary: equal published
roots ⟹ equal committed tuples. **These two are exactly what made the published PI `NEW_COMMIT` bind
the ACTUAL post-state.** That binding is no longer a Boolean fact of the AIR here; downstream it is
now carried by a NEGLIGIBLE-ADVANTAGE bound on an equivocation game, and it must be read as one — a
bounded-query adversary's chance, not an impossibility.

**Why they were vacuous.** Both were conditioned on `CommitTreeInjective H`, and that hypothesis is
FALSE at every deployed parameter: `Spike.CommitTreeRegrounded.commitTreeInjective_false_babyBear`
and `commitTreeInjective_false_blake3` refute it outright. The carrier is injectivity of
`commitTree H` on the INFINITE `List ℤ` of committed columns while the root is ONE felt;
`commitTree_bounded` proves the tree inherits `H`'s window (the 12-column branch IS an `H` output,
the malformed-tuple fallback is `0`, in-window), which is what lets the refutation be stated on `H`
rather than on the tree. Counting, not cryptanalysis. `#assert_axioms` audits the PROOF and never
the HYPOTHESIS, so both theorems were kernel-clean and said nothing about any deployed circuit —
which is worse than absent, because they read as the result.

**Consume instead — `Spike.CommitTreeRegrounded`.**
* PREFER the ROM-DISCHARGED forms: `state_commitment_binds_state_rom` and
  `state_commitment_no_silent_change_rom`. Every query-bounded equivocator of the published
  `NEW_COMMIT` has NEGLIGIBLE advantage in the keyed ROM. They carry NO floor hypothesis and no cost
  model — only a polynomial query budget (`PolyBounded`) and the adversary's membership in the query
  class — over the PROVED floor `keyedRom_hard` (the birthday bound).
* The advantage-bound layer beneath them: `state_commitment_binds_state_advantage_bound` and
  `state_commitment_no_silent_change_advantage_bound`, from the REAL state-equivocation game
  (`stateEquivocationGame` — the adversary exhibits two DISTINCT post-state tuples behind ONE
  published root, which IS the attack these deleted theorems ruled out) via
  `equivocationToCollisionFinder`, each carrying an EXPLICIT undischarged `Eff`.

`CommitTreeInjective` and `commitTree` are KEPT. The refutations above name the def, so deleting it
would delete the proof that it is false, and `Verify/FloorRatchet.lean` hard-errors on a carrier
missing from its baseline. It is a tombstone WITH TEETH: the accrual stop that keeps a new vacuous
floor from appearing under this portal. -/

/-!
## Verdict (extends the in-circuit-vs-deferred ledger)

* **SetField** → `setfield_targets_exactly_one_field` proves the per-field gate (air.rs:606)
  freezes every non-target field and the sum constraint (air.rs:636) pins the single target
  field's delta (as a field congruence; `setfield_target_value_pinned` upgrades to the integer
  equation under an honest magnitude bound). The HEADLINE caveat is exposed as a theorem:
  `setfield_aux_honesty_gap` exhibits a concrete satisfying trace where a LYING `aux[0]`
  (air.rs:629, a free witness column) makes the target field land at the wrong value while both
  constraints still hold — so SetField *intended-value correctness* is NOT in-circuit; it rests
  on off-circuit honesty of `old_value_at_idx`.
* **balance_hi range-check** → `balance_hi_in_range` proves the HIGH limb ∈ [0,2^30), the twin
  of the prior spike's lo-limb soundness, completing the post-state balance range proof for both
  limbs. Honest note in-proof: the lane is 30 bits (not 34); 30 is the soundness-mandated width
  because `2^30 < p` keeps the in-field recomposition unique and non-wrapping.
* **state_commitment binding** → the SHAPE is here (`commitTree`, air.rs:2540–2543, plus the
  last-row boundary pin at air.rs:2707–2711); the BINDING is NOT. The two consumers that asserted
  it — `state_commitment_binds_state` / `state_commitment_no_silent_change` — were conditioned on
  `CommitTreeInjective H`, which `CommitTreeRegrounded` PROVES FALSE at BabyBear and at blake3, and
  are DELETED. Read `CommitTreeRegrounded.state_commitment_binds_state_rom` /
  `state_commitment_no_silent_change_rom` instead: the published `NEW_COMMIT` binds the post-state
  up to a NEGLIGIBLE equivocation advantage on the PROVED keyed-ROM floor.

STILL DEFERRED (honest): the collision-resistance of Poseidon2 itself (§8 primitive, a carried
assumption); SetField intended-value correctness (depends on off-circuit `aux[0]` honesty);
cross-cell two-party conservation (turn/net-delta scope, not a single-row constraint).
-/

end Dregg2.Spike.EffectVmConstraints2

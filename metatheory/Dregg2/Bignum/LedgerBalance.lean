/-
# Dregg2.Bignum.LedgerBalance — the SIGNED ledger balance, read at the width it is actually carried.

**SUBSTRATE, SAID OUT LOUD: this is Lean.** Everything here is a Lean model of the deployed felt
encoding plus INSTANTIATIONS of `Dregg2.Bignum`. No constraint is hand-written in Rust by this
module, no descriptor is registered, no emit path is touched, no VK moves. The `Constraint`-level
gate ties this work would eventually ride are already Lean-authored and already proved
(`Dregg2.Bignum.subLimbEqn_is_gate` / `addLimbEqn_is_gate`); nothing new is authored in Rust.

## The object

`dregg_cell::CellState::balance` is an **`i64`** (`cell/src/state.rs:204`) — SIGNED by design: THE
EPOCH §5's signed value model, where the issuer well legitimately carries `−supply`
(`CellState::well_debit_balance` `:759`, `apply_balance_change_well` `:1137`, both of which permit a
NEGATIVE result, unlike `debit_balance` `:740`).

That signed `i64` reaches the circuit and the light client through ONE encoder:

```rust
// turn/src/rotation_witness.rs:106-117 — the r0/r2 rotated-block weld values
pub fn balance_lo_felt(balance: i64) -> BabyBear { split_u64(balance as u64).0 }
pub fn balance_hi_felt(balance: i64) -> BabyBear { split_u64(balance as u64).1 }
// circuit/src/effect_vm/helpers.rs:13-17
pub fn split_u64(val: u64) -> (BabyBear, BabyBear) {
    let lo = (val & 0x3FFF_FFFF) as u32;   // low 30 bits
    let hi = (val >> 30) as u32;           // "upper 34 bits" — then BabyBear::new REDUCES mod p
    (BabyBear::new(lo), BabyBear::new(hi))
}
// turn/src/executor/proof_verify.rs:92 — the documented inverse
let balance = lo | (hi << 30);
```

Two facts follow and neither is decoration:

1. the cast `balance as u64` is **two's complement** — the sign is not encoded, it is *reinterpreted*;
2. the high limb is a 34-bit quantity pushed into ONE BabyBear felt, so `BabyBear::new` **reduces it
   mod `p`** — the encoder is not injective.

`§2` and `§3` state both as theorems over ℤ, at the deployed constants. `§4` states the tooth that
DOES catch (2) and shows it does NOT catch (1). `§5`–`§7` are the `Dregg2.Bignum` adoption.

## What is PROVED here

  * `sign_wound_survives_the_range_check` — `−1` encodes to two limbs that BOTH satisfy the deployed
    in-circuit 30-bit range proof, and the documented inverse reads a value above `10^18`.
  * `deployedEnc_not_injective` — two distinct balances, identical limbs, identical commitment.
  * `aliasing_dominated_in_circuit` — and why (2) is nonetheless the LESSER of the two: the 30-bit
    range proof caps the admitted join at `2^60 < 2^30·p`, so the alias partner is out of range.
    (1) has no such tooth. **A wound with a tooth and a wound without one must be priced apart.**
  * `deployedDebit_is_bignum_sub` — the DEPLOYED frozen-`bal_hi` debit gate *already is* a
    `Dregg2.Bignum.SubValid` witness at two limbs, with the amount's high limb pinned `0` and the
    inter-limb borrow structurally forced to `0`. The repair is therefore not a new construction: it
    is un-pinning one column.
  * `deployedDebit_cannot_cross_limb` / `bignum_admits_cross_limb_spend` — the same honest spend the
    deployed gate cannot witness IS witnessed by the two-limb borrow chain. The frozen high limb is
    a LIVENESS wall, not a hardening.
  * `balLimbs_injective`, `debit_exact`, `debit_iff`, `debit_underflow_unsat`, `credit_*` — the
    library instantiated at the deployed limb base.

## What is NOT proved here (read this before quoting anything above)

  * **That the Rust producer computes `deployedLo`/`deployedHi`.** That is a Rust↔Lean
    correspondence, not a Lean theorem, and writing it as one would be a name rather than a proof.
    The instrument that would pin it is a differential test against `balance_lo_felt` /
    `balance_hi_felt`, in the shape of `circuit/tests/effect_vm_commit_lean_differential.rs`.
  * **That any deployed descriptor's emitted gate set entails `DeployedDebit` at its columns.**
    `DeployedDebit` is transcribed from `EffectVmEmitTransfer`'s gate list; the weld to
    `Satisfied2`/`transferAvail_derives_availability_row` is not made here.
  * **Anything about the hardened `*Avail` faces' 15-bit borrow chain.** That closure is real and
    deployed (`docs/FINDING-modp-wrap-forgery-audit.md`); it hardens the LOW limb. Nothing here
    weakens it and nothing here re-litigates it.
-/
import Dregg2.Bignum
import Dregg2.Bignum.DigitInjective

namespace Dregg2.Bignum.LedgerBalance

open Dregg2.Circuit.CaveatBignum

set_option autoImplicit false

/-! ## §1 — The deployed constants and the deployed encoder, as functions on ℤ. -/

/-- `split_u64`'s low-limb width: `val & 0x3FFF_FFFF` is base `2^30`. This is also
`DescriptorIR2.BAL_LIMB_BITS = 30`, the width of the in-circuit range proof on BOTH balance limbs
(`circuit/src/effect_vm/helpers.rs:291-302`, `fill_balance_limb_bits`). -/
def limbBase : ℤ := 1073741824

/-- The BabyBear modulus `p = 2^31 − 2^27 + 1`. `BabyBear::new` reduces its argument mod `p`. -/
def babyBearP : ℤ := 2013265921

/-- The `balance as u64` cast: reinterpretation modulo `2^64`. -/
def wordMod : ℤ := 18446744073709551616

theorem limbBase_pos : 0 < limbBase := by norm_num [limbBase]

theorem babyBearP_pos : 0 < babyBearP := by norm_num [babyBearP]

/-- `split_u64(balance as u64).0` — the low balance limb the trace and the `r0` weld carry.
(`Int`'s `%` is `emod`, which is non-negative for a positive modulus, so this IS the u64 cast
followed by the 30-bit mask.) -/
def deployedLo (b : ℤ) : ℤ := (b % wordMod) % limbBase

/-- `split_u64(balance as u64).1` — the high balance limb, AFTER `BabyBear::new`'s mod-`p`
reduction. The `>> 30` of a u64 is a 34-bit quantity; the felt holds ~31 bits. -/
def deployedHi (b : ℤ) : ℤ := ((b % wordMod) / limbBase) % babyBearP

/-- `turn/src/executor/proof_verify.rs:92`'s `lo | (hi << 30)` — the documented inverse, i.e. what a
consumer reads back out of the two committed limbs. -/
def deployedJoin (lo hi : ℤ) : ℤ := lo + limbBase * hi

/-! ## §2 — THE SIGN WOUND.

The issuer well's balance is legitimately negative. The encoder is a two's-complement
reinterpretation, so a negative balance is not rejected, not flagged, and not out of range — it is
read as a very large positive one. -/

/-- The low limb of `−1` is `2^30 − 1`: the largest value the low limb can hold. This is the number
a consumer that reads `BALANCE_LO` alone — which is what the Lean refinement tower welds the kernel
ledger to (`CircuitCompleteness.lean:280-283`, `srcPre.balLo = pre.kernel.bal tr.src a`) — sees for
a cell whose true balance is `−1`. -/
theorem deployedLo_negOne : deployedLo (-1) = 1073741823 := by
  norm_num [deployedLo, wordMod, limbBase]

/-- The high limb of `−1` is `(2^34 − 1) mod p = 1073741815`. -/
theorem deployedHi_negOne : deployedHi (-1) = 1073741815 := by
  norm_num [deployedHi, wordMod, limbBase, babyBearP]

/-- ⚑ **THE HEADLINE.** The deployed in-circuit range proof pins both balance limbs into
`[0, 2^30)`. The encoding of `−1` satisfies BOTH pins — the high limb clears the bound by **nine** —
and the documented inverse reads back a value above `10^18`.

So: the tooth that exists (the 30-bit range proof, `fill_balance_limb_bits`) is not a tooth against
a NEGATIVE balance at all. A cell at `−1` presents a light-client-visible low limb of
`1,073,741,823` and a joined value of ~`1.15 × 10^18`. Nothing in the range discipline says
otherwise, because the range discipline was designed against a mod-`p` *wrap*, and this is a
two's-complement *reinterpretation* — a different failure with the same symptom. -/
theorem sign_wound_survives_the_range_check :
    (0 ≤ deployedLo (-1) ∧ deployedLo (-1) < limbBase)
      ∧ (0 ≤ deployedHi (-1) ∧ deployedHi (-1) < limbBase)
      ∧ 1000000000000000000 < deployedJoin (deployedLo (-1)) (deployedHi (-1)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;>
    simp only [deployedLo_negOne, deployedHi_negOne, deployedJoin, limbBase] <;> norm_num

/-- NON-VACUITY, the other pole: the encoder is FAITHFUL on the non-negative in-range domain. For
`0 ≤ b < 2^60` the two limbs rejoin to `b` exactly. So §2 is a statement about the SIGNED and
OVER-WIDE domain specifically — it is not a claim that the encoder is broken everywhere, and a
repair must preserve this half. -/
theorem deployedJoin_faithful_on_range (b : ℤ) (h0 : 0 ≤ b) (hb : b < limbBase * limbBase) :
    deployedJoin (deployedLo b) (deployedHi b) = b := by
  have hw : b % wordMod = b := by
    apply Int.emod_eq_of_lt h0
    simp only [wordMod, limbBase] at hb ⊢
    omega
  have hlt : b / limbBase < limbBase := by
    apply Int.ediv_lt_of_lt_mul limbBase_pos
    linarith [hb]
  have hge : 0 ≤ b / limbBase := Int.ediv_nonneg h0 (le_of_lt limbBase_pos)
  have hp : b / limbBase < babyBearP := by
    simp only [limbBase, babyBearP] at hlt ⊢; omega
  have hhi : deployedHi b = b / limbBase := by
    simp only [deployedHi, hw]
    exact Int.emod_eq_of_lt hge hp
  have hlo : deployedLo b = b % limbBase := by simp only [deployedLo, hw]
  simp only [deployedJoin, hhi, hlo]
  have := Int.emod_add_ediv b limbBase
  linarith [this]

/-! ## §3 — THE NON-INJECTIVITY.

The high limb is a 34-bit quantity in a ~31-bit felt. `BabyBear::new` reduces it. So the encoder
identifies balances `2^30 · p` apart. -/

/-- ⚑ **`deployedEnc_not_injective`.** Two DISTINCT balances with IDENTICAL limbs — hence an
identical per-cell commitment, since the commitment absorbs exactly `[bal_lo, bal_hi, nonce, …]`
(`circuit/tests/effect_vm_commit_lean_differential.rs:26-30`). The witness pair is
`0` and `2^30 · p = 2,161,727,822,211,579,904`, both inside `i64`. -/
theorem deployedEnc_not_injective :
    ∃ a b : ℤ, a ≠ b ∧ deployedLo a = deployedLo b ∧ deployedHi a = deployedHi b := by
  refine ⟨0, limbBase * babyBearP, ?_, ?_, ?_⟩
  · norm_num [limbBase, babyBearP]
  · norm_num [deployedLo, wordMod, limbBase, babyBearP]
  · norm_num [deployedHi, wordMod, limbBase, babyBearP]

/-! ## §4 — THE TOOTH, and what it does and does not reach.

⚑ The whole lesson of the felt-width re-pricing is that WIDTH BOUNDS THE IMAGE, IT DOES NOT PRICE
THE ATTACK. So both §2 and §3 must be priced against the teeth that actually run. There is exactly
one: the in-circuit 30-bit range proof on both limbs. It reaches §3. It does not reach §2. -/

/-- The 30-bit range proof caps the joined value at `2^60`. -/
theorem admitted_join_lt_2_60 {lo hi : ℤ}
    (hlo0 : 0 ≤ lo) (hloB : lo < limbBase) (hhi0 : 0 ≤ hi) (hhiB : hi < limbBase) :
    deployedJoin lo hi < limbBase * limbBase := by
  simp only [deployedJoin, limbBase] at hloB hhiB hlo0 hhi0 ⊢
  omega

/-- ⚑ **`aliasing_dominated_in_circuit`.** `2^60 < 2^30 · p`, so for any limb pair the range proof
admits, the alias partner from §3 is OUT of the admitted range. **The non-injectivity of the high
limb is DOMINATED wherever the in-circuit range proof runs** — it is live only on host paths that
call `split_u64` without it. Priced honestly, §3 ranks BELOW §2, which has no tooth at all. -/
theorem aliasing_dominated_in_circuit {lo hi : ℤ}
    (hlo0 : 0 ≤ lo) (hloB : lo < limbBase) (hhi0 : 0 ≤ hi) (hhiB : hi < limbBase) :
    deployedJoin lo hi < limbBase * babyBearP := by
  have h := admitted_join_lt_2_60 hlo0 hloB hhi0 hhiB
  simp only [limbBase, babyBearP] at h ⊢
  omega

/-! ## §4b — THE SAME ENCODER WITH NO HIGH LIMB AT ALL: the note accumulator leaf.

`cell/src/commitment_set.rs:263-272` commits a note's `u64` value as `split_u64(value).0` — the LOW
limb ALONE:

```rust
pub fn accumulator_leaf(commitment: &[u8; 32], value: u64) -> HeapLeaf {
    HeapLeaf::entry(fold_bytes32_to_bb(commitment), split_u64(value).0)
}
```

and so does the nullifier set (`cell/src/nullifier_set.rs:458`) and both circuit twins
(`circuit/src/effect_vm/trace_rotated.rs:1568` `nf_value`, `:1805` `cm_value`). A `NOTE_VALUE_HI`
param column IS written (`circuit/src/effect_vm/trace.rs:743,753`) and is read by nothing.

This is the SAME `deployedLo` projection as the balance's low limb — but with no companion limb
committed anywhere, so §4's tooth has nothing to bite: the aliasing period is `2^30`, not `2^60`,
and it is a SOUNDNESS shape (the committed set cannot testify to the value the host credited)
rather than the balance's liveness shape. -/

/-- ⚑ **The accumulator leaf aliases at `2^30`.** Two note values a mere `2^30` apart — both far
inside `u64`, both perfectly ordinary — produce the SAME committed leaf value. Compare
`aliasing_dominated_in_circuit`: there the alias partner sat above the range proof's ceiling; here
there is no second limb and therefore no ceiling. -/
theorem accumulatorLeaf_aliases_at_2_30 :
    ∃ v w : ℤ, v ≠ w ∧ 0 ≤ v ∧ 0 ≤ w ∧ v < wordMod ∧ w < wordMod
      ∧ deployedLo v = deployedLo w := by
  refine ⟨0, limbBase, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [deployedLo, wordMod, limbBase]

/-! ## §5 — THE ADOPTION: the balance as a `Dregg2.Bignum` limb vector.

`balVal` is `CaveatBignum.bignumVal` at the deployed limb base — the SAME denotation every
`Dregg2.Bignum` keystone is stated over. Nothing is re-derived below; every theorem in this section
is an application. -/

/-- The ledger balance denoted by a limb vector, at the deployed base `2^30`. -/
def balVal (limbs : List ℤ) : ℤ := bignumVal limbBase limbs

/-- ⚑ **INJECTIVE — provably, not merely wider.** A ranged limb vector of fixed length is UNIQUELY
determined by the balance it denotes. Contrast `deployedEnc_not_injective`: the deployed pair is
non-injective *because* the high limb is reduced mod `p`, and the fix is not "more felts", it is
"every limb range-checked below the base". `Ranged` is the load-bearing hypothesis — drop it and the
statement is FALSE (`DigitInjective`'s own negative pole). -/
theorem balLimbs_injective {xs ys : List ℤ} (hlen : xs.length = ys.length)
    (hrx : Ranged limbBase xs) (hry : Ranged limbBase ys) (h : balVal xs = balVal ys) : xs = ys :=
  DigitInjective.bignumVal_injective limbBase_pos xs ys hlen hrx hry h

/-- A ranged balance vector denotes a non-negative integer that FITS its width — so mapping it into
a field of size `≥ (2^30)^n` cannot wrap. -/
theorem balVal_fits (xs : List ℤ) (hr : Ranged limbBase xs) :
    0 ≤ balVal xs ∧ balVal xs < limbBase ^ xs.length :=
  ⟨bignumVal_nonneg (le_of_lt limbBase_pos) xs hr,
   bignumVal_lt_base_pow limbBase_pos xs hr⟩

/-- A DEBIT is the library's borrow subtraction at the deployed base. -/
def DebitValid (bal amt bal' : List ℤ) : Prop := SubValid limbBase bal amt bal'

/-- A CREDIT is the library's carry addition at the deployed base, top carry pinned `0`. -/
def CreditValid (bal amt bal' : List ℤ) : Prop := AddValid limbBase bal amt bal' 0

/-- **DEBIT SOUNDNESS.** A valid debit moves the balance by EXACTLY the amount, over ℤ — not mod
`p`, and across the whole limb vector rather than the low limb alone. -/
theorem debit_exact (bal amt bal' : List ℤ) (h : DebitValid bal amt bal') :
    balVal bal' = balVal bal - balVal amt :=
  subVal bal amt bal' h

/-- **DEBIT SOUNDNESS + COMPLETENESS.** A debit witness EXISTS iff the cell genuinely owns the
funds. Both directions matter: `←` is the LIVENESS the deployed frozen-`bal_hi` gate lacks (§6),
`→` is the soundness. -/
theorem debit_iff (bal amt : List ℤ) (hlen : amt.length = bal.length)
    (hra : Ranged limbBase amt) (hrb : Ranged limbBase bal) :
    (∃ bal', DebitValid bal amt bal') ↔ balVal amt ≤ balVal bal :=
  sub_iff limbBase_pos bal amt hlen hra hrb

/-- ⚑ **THE ANTI-MINT TOOTH.** A debit exceeding the balance has NO witness. This is the
`sub_underflow_unsat` keystone at the deployed base: the wraparound-to-a-huge-balance mint is
UNCONSTRUCTABLE, over the FULL limbed balance rather than the low limb. -/
theorem debit_underflow_unsat (bal amt : List ℤ) (hlen : amt.length = bal.length)
    (hra : Ranged limbBase amt) (hrb : Ranged limbBase bal)
    (hunder : balVal bal < balVal amt) :
    ¬ ∃ bal', DebitValid bal amt bal' :=
  sub_underflow_unsat limbBase_pos bal amt hlen hra hrb hunder

/-- **CREDIT SOUNDNESS.** A valid credit moves the balance by exactly the amount, over ℤ. -/
theorem credit_exact (bal amt bal' : List ℤ) (h : CreditValid bal amt bal') :
    balVal bal' = balVal bal + balVal amt := by
  have := addValid_val bal amt bal' 0 h
  simpa [balVal] using this

/-- ⚑ **THE ANTI-OVERFLOW TOOTH.** A credit whose true sum does not fit the declared width has NO
witness — the field cannot be made to wrap a balance upward either. -/
theorem credit_overflow_unsat (bal amt : List ℤ) (hlen : bal.length = amt.length)
    (hrb : Ranged limbBase bal) (hra : Ranged limbBase amt)
    (hover : limbBase ^ bal.length ≤ balVal bal + balVal amt) :
    ¬ ∃ bal', CreditValid bal amt bal' := by
  have h := add_overflow_unsat limbBase_pos bal amt 0 hlen hrb hra (Or.inl rfl) (by
    simpa [balVal] using hover)
  simpa [CreditValid] using h

/-! ## §6 — THE DEPLOYED GATE IS ALREADY A `SubValid` — WITH ONE COLUMN PINNED TO ZERO.

The deployed EffectVM transfer/mint/burn gate set contains, verbatim
(`Dregg2/Circuit/Emit/EffectVmEmitTransfer.lean` header; `EffectVmEmitBurn.gBalHiFix:130`;
`EffectVmEmitMint.gBalHiFix:134`):

    new_bal_lo − old_bal_lo − amount = 0      (the move, on the LOW limb)
    new_bal_hi − old_bal_hi = 0               (the high limb FROZEN)

plus the 30-bit range proof on the after-limbs. `DeployedDebit` transcribes exactly that. -/

/-- The deployed frozen-`bal_hi` debit gate, transcribed. -/
def DeployedDebit (lo hi amt lo' hi' : ℤ) : Prop :=
  hi' = hi ∧ lo' = lo - amt ∧ 0 ≤ lo' ∧ lo' < limbBase

/-- The deployed gate does move the FULL two-limb value by exactly `amt` — where it fires. -/
theorem deployedDebit_exact {lo hi amt lo' hi' : ℤ} (h : DeployedDebit lo hi amt lo' hi') :
    balVal [lo', hi'] = balVal [lo, hi] - amt := by
  obtain ⟨hhi, hlo, _, _⟩ := h
  simp only [balVal, bignumVal_cons, bignumVal_nil, hhi, hlo]
  ring

/-- ⚑ **THE ADOPTION THEOREM.** The DEPLOYED gate *already is* a `Dregg2.Bignum.SubValid` witness at
two limbs — with the amount's HIGH limb pinned to the constant `0` and, in consequence, the
inter-limb borrow forced to `0` by the frozen-`bal_hi` equation.

Read the other way: the repair is not a new construction and not new combinatorics. It is
**un-pinning one column** — letting the amount carry a high limb and letting the borrow be a real
witness bit — after which `debit_exact` / `debit_iff` / `debit_underflow_unsat` apply verbatim. The
hypothesis `0 ≤ hi < limbBase` is exactly the deployed 30-bit range proof on `bal_hi`; nothing is
assumed that the trace does not already carry. -/
theorem deployedDebit_is_bignum_sub {lo hi amt lo' hi' : ℤ}
    (hhi0 : 0 ≤ hi) (hhiB : hi < limbBase)
    (h : DeployedDebit lo hi amt lo' hi') :
    DebitValid [lo, hi] [amt, 0] [lo', hi'] := by
  obtain ⟨hhi, hlo, hnn, hlt⟩ := h
  refine ⟨0, Or.inl rfl, by omega, hnn, hlt, ?_⟩
  exact ⟨0, Or.inl rfl, by omega, by omega, by omega, rfl⟩

/-- ⚑ **THE LIVENESS WALL, EXHIBITED.** A cell holding exactly `2^30` (limbs `[0, 1]`) spending ONE
unit — an entirely honest move, and the funds are genuinely there — has NO deployed-gate witness.
The high limb is frozen, so no borrow can cross the limb boundary, and the low-limb equation demands
`lo' = 0 − 1 = −1`, which the range proof refuses.

This is not a hardening. Every balance at or above `2^30` is unspendable down through the boundary,
and the `*Avail` borrow-chain hardening does not reach it: that chain runs on the LOW limb. -/
theorem deployedDebit_cannot_cross_limb :
    ¬ ∃ lo' hi', DeployedDebit 0 1 1 lo' hi' := by
  rintro ⟨lo', hi', _, hlo, hnn, _⟩
  omega

/-- The funds in the previous theorem really are there: `balVal [0, 1] = 2^30 ≥ 1`. So the refusal
is a refusal of an HONEST spend, not a correct rejection. (Stating the impossibility without this
would be exactly the "true for free" trap — a gate that refuses a spend nobody can afford is not a
wound.) -/
theorem cross_limb_spend_is_honest : (1 : ℤ) ≤ balVal [0, 1] := by
  simp only [balVal, bignumVal_cons, bignumVal_nil, limbBase]
  norm_num

/-- Both limb vectors involved are ranged — the hypothesis the library needs, discharged. -/
theorem ranged_pair {a b : ℤ} (ha0 : 0 ≤ a) (haB : a < limbBase)
    (hb0 : 0 ≤ b) (hbB : b < limbBase) : Ranged limbBase [a, b] := by
  intro z hz
  rcases List.mem_cons.mp hz with h1 | h1
  · exact h1 ▸ ⟨ha0, haB⟩
  · rcases List.mem_cons.mp h1 with h2 | h2
    · exact h2 ▸ ⟨hb0, hbB⟩
    · simp at h2

/-- ⚑ **THE REPAIR ADMITS WHAT THE DEPLOYED GATE REFUSES.** The very spend
`deployedDebit_cannot_cross_limb` has no witness for IS witnessed by the two-limb borrow chain. So
the conversion is a strict improvement in BOTH directions: `debit_underflow_unsat` refutes every
over-debit (soundness) and this exhibits the honest cross-limb spend (liveness). A repair that only
tightened would be a different bug. -/
theorem bignum_admits_cross_limb_spend :
    ∃ bal', DebitValid [0, 1] [1, 0] bal' := by
  refine (debit_iff [0, 1] [1, 0] rfl ?_ ?_).mpr ?_
  · exact ranged_pair (by norm_num) (by norm_num [limbBase]) (by norm_num)
      (by norm_num [limbBase])
  · exact ranged_pair (by norm_num) (by norm_num [limbBase]) (by norm_num)
      (by norm_num [limbBase])
  · simp only [balVal, bignumVal_cons, bignumVal_nil, limbBase]
    norm_num

/-! ## §7 — THE SIGNED DOMAIN: what `Dregg2.Bignum` does NOT cover, and the bias that closes it.

`Dregg2.Bignum` is a NON-NEGATIVE positional system (`bignumVal_nonneg`), so a limbed balance can
never denote the issuer well's `−supply`. Adopting it for a SIGNED ledger therefore needs one more
step, and the tree already has the right one — on the BYTE path only:

    // cell/src/state.rs:1186
    pub fn balance_biased(balance: i64) -> u64 { (balance as u64) ^ (1u64 << 63) }

which is order-preserving and injective, and is used by `encode_balance_le`. The FELT path
(`balance_lo_felt` / `balance_hi_felt`) does **not** use it — it uses the raw cast. That divergence
between the two encodings of the same value is §2's root. -/

/-- The bias, over ℤ: `b ↦ b + 2^63`. (On `i64` the XOR of the sign bit and the addition of `2^63`
agree; over ℤ the addition is the honest statement.) -/
def biased (b : ℤ) : ℤ := b + 9223372036854775808

/-- The bias is injective. -/
theorem biased_injective : Function.Injective biased := by
  intro a b h
  simp only [biased] at h
  omega

/-- The bias is order-preserving — so a comparison on biased limbs IS the signed comparison, and
`Dregg2.Bignum.le_iff` / `lt_iff` transport to signed balances without a separate order theory. -/
theorem biased_lt {a b : ℤ} : biased a < biased b ↔ a < b := by
  simp only [biased]; omega

/-- The bias maps the whole `i64` domain into `[0, 2^64)` — the domain `Ranged` limbs can hold. -/
theorem biased_range {b : ℤ} (h1 : -9223372036854775808 ≤ b) (h2 : b < 9223372036854775808) :
    0 ≤ biased b ∧ biased b < wordMod := by
  simp only [biased, wordMod]; omega

/-- Three 30-bit limbs cover `2^90`, with room over the `2^64` the biased domain needs. -/
theorem three_limbs_cover_biased : wordMod < limbBase ^ 3 := by
  norm_num [wordMod, limbBase]

/-- The canonical three-limb decomposition of a biased balance. -/
def biasedLimbs (b : ℤ) : List ℤ :=
  [ biased b % limbBase
  , biased b / limbBase % limbBase
  , biased b / limbBase / limbBase ]

/-- ⚑ **THE COMPLETENESS POLE — PROVED.** Every `i64` balance HAS a valid three-limb biased
representation: the vector is ranged and denotes the biased balance. With the bias range
`[0, 2^64)` and the base `2^30`, each limb bound and the two-step Euclidean identity are linear
facts over literal divisors, which `omega` closes.

**Why the uniqueness pole keeps `Ranged`:** dropping it from `biasedLimbs_unique` would make that
theorem FALSE, not merely weaker (`DigitInjective`'s negative pole exhibits
`[128,0]` and `[0,1]` colliding at base 128 without it). ⚑ A wider encoder that is not PROVED
injective is the same bug with better optics. -/
theorem biasedLimbs_valid (b : ℤ) (h1 : -9223372036854775808 ≤ b) (h2 : b < 9223372036854775808) :
    (biasedLimbs b).length = 3 ∧ Ranged limbBase (biasedLimbs b)
      ∧ balVal (biasedLimbs b) = biased b := by
  have hr := biased_range h1 h2
  simp only [wordMod] at hr
  refine ⟨rfl, ?_, ?_⟩
  · intro y hy
    simp only [biasedLimbs, List.mem_cons, List.not_mem_nil, or_false] at hy
    simp only [limbBase] at hy ⊢
    rcases hy with rfl | rfl | rfl <;> omega
  · simp only [balVal, biasedLimbs, bignumVal_cons, bignumVal_nil, limbBase]
    omega

/-- ⚑ **THE SOUNDNESS POLE — PROVED.** The three-limb biased representation is UNIQUE: a ranged
three-limb vector is determined by the balance it denotes. Together with `biased_injective`, two
DISTINCT signed balances have DISTINCT limb vectors — which is precisely what
`deployedEnc_not_injective` says the deployed pair does not do.

Note what this does NOT say: it says nothing about the HASH that absorbs the limbs (that is a
separate, computational, `Poseidon2SpongeCR` assumption), and nothing about any emitted column. It
is the packing layer only. -/
theorem biasedLimbs_unique {xs ys : List ℤ}
    (hx : xs.length = 3) (hy : ys.length = 3)
    (hrx : Ranged limbBase xs) (hry : Ranged limbBase ys)
    (h : balVal xs = balVal ys) : xs = ys :=
  balLimbs_injective (hx.trans hy.symm) hrx hry h

/-! ## §8 — NON-VACUITY at the deployed constants, both poles.

Every theorem above that could be true for free is exhibited firing in both directions here. -/

-- The deployed encoder ALIASES: two distinct balances, one limb pair.
example : ∃ a b : ℤ, a ≠ b ∧ deployedLo a = deployedLo b ∧ deployedHi a = deployedHi b :=
  deployedEnc_not_injective

-- …and the in-circuit range proof DOES exclude the alias partner (the tooth fires).
example : deployedJoin 5 7 < limbBase * babyBearP :=
  aliasing_dominated_in_circuit (by norm_num) (by norm_num [limbBase]) (by norm_num)
    (by norm_num [limbBase])

-- …but it does NOT exclude the sign wound (the tooth does not fire).
example : deployedHi (-1) < limbBase := (sign_wound_survives_the_range_check.2.1).2

-- The deployed gate REFUSES an honest cross-limb spend…
example : ¬ ∃ lo' hi', DeployedDebit 0 1 1 lo' hi' := deployedDebit_cannot_cross_limb

-- …and the limbed repair ADMITS it.
example : ∃ bal', DebitValid [0, 1] [1, 0] bal' := bignum_admits_cross_limb_spend

-- The anti-mint tooth FIRES on the limbed representation: 2^30 cannot pay 2·2^30.
example : ¬ ∃ bal', DebitValid [0, 1] [0, 2] bal' := by
  refine debit_underflow_unsat [0, 1] [0, 2] rfl ?_ ?_ ?_
  · exact ranged_pair (by norm_num) (by norm_num [limbBase]) (by norm_num)
      (by norm_num [limbBase])
  · exact ranged_pair (by norm_num) (by norm_num [limbBase]) (by norm_num)
      (by norm_num [limbBase])
  · simp only [balVal, bignumVal_cons, bignumVal_nil, limbBase]
    norm_num

/-! ## §AXIOM HYGIENE. -/

#assert_axioms deployedLo_negOne
#assert_axioms deployedHi_negOne
#assert_axioms sign_wound_survives_the_range_check
#assert_axioms deployedJoin_faithful_on_range
#assert_axioms deployedEnc_not_injective
#assert_axioms aliasing_dominated_in_circuit
#assert_axioms accumulatorLeaf_aliases_at_2_30
#assert_axioms balLimbs_injective
#assert_axioms debit_exact
#assert_axioms debit_iff
#assert_axioms debit_underflow_unsat
#assert_axioms credit_exact
#assert_axioms credit_overflow_unsat
#assert_axioms deployedDebit_exact
#assert_axioms deployedDebit_is_bignum_sub
#assert_axioms deployedDebit_cannot_cross_limb
#assert_axioms bignum_admits_cross_limb_spend
#assert_axioms biased_injective
#assert_axioms biased_lt
#assert_axioms biasedLimbs_valid
#assert_axioms biasedLimbs_unique

end Dregg2.Bignum.LedgerBalance

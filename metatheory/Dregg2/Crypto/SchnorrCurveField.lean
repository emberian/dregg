/-
# Dregg2.Crypto.SchnorrCurveField — the soundness STRUCTURE under the in-circuit Schnorr curve.

The confidential-VALUE path runs an in-circuit Schnorr signature over an elliptic curve defined over
`BabyBear^8 = F_p[z]/(z^8 - 11)` (`p = 2^31 - 2^27 + 1`). The Rust field/curve primitives
(`circuit/src/babybear8.rs`, `circuit/src/schnorr_curve.rs`) rebuilt this to a REAL field over a
PRIME-order curve and pin it with Rust tests + a PARI point-count.

⚠ **RETIREMENT NOTE (2026-07-16).** The Rust AIR this file's §3 pillar mirrored,
`circuit/src/schnorr_air.rs`, was DELETED (commit `f7d09d5f5`) as dead pre-law hand-authored algebra —
591 lines, no Lean twin, unassured, reachable only through the never-live-wired `turn_auth_signature_air`.
So the theorems below remain kernel-clean structure results, but their DEPLOYED anchor for the AIR-side
pillar (§3) is retired: there is currently NO deployed in-circuit Schnorr verification AIR. Per architectural
law #1, when a confidential-value signature circuit is deployed it must be EMITTED FROM LEAN
(`Dregg2/Circuit/Emit/*.lean`), not hand-authored — at which point this structure discharges its emission,
not a corpse. `babybear8.rs` + `schnorr_curve.rs` (the field/curve primitives) DO still exist and are cited
truthfully above; only the AIR limb was dead.

Three facts carry the soundness of that rebuild. This file separates, for each, the part that is a
genuine THEOREM (provable structure — formalized here, kernel-clean) from the part that stays a
typed empirical PRIMITIVE (a finite computation PARI/Rust verified — a named hypothesis, exactly the
`Ed25519Reduction.Ed25519EufCma` / `PortalFloor` discipline). The split is the whole point: the Rust
property-tests (`is_a_field_no_zero_divisors`, `generator_has_order_n`, the forged-`R` tooth) are
each checking a *consequence* of an empirical fact, and the consequence is a theorem — so the theorem
belongs in Lean and only the empirical seed stays a hypothesis.

## The three pillars

1. **"It's a field" (no zero divisors).** EMPIRICAL SEEDS: `p = 2^31 - 2^27 + 1` is prime (so
   `ZMod p` = BabyBear is a field) and `z^8 - 11` is irreducible over `F_p` (PARI: it factors as a
   single degree-8 irreducible). THEOREM (here): in ANY field, a nonzero element is a unit and there
   are NO zero divisors — and, threading BOTH seeds, the REAL tower `(ZMod p)[X]/(z^8-11) = BabyBear^8`
   IS a field (`babybear_tower_no_zero_divisors` / `_nonzero_isUnit`), so the Rust
   `is_a_field_no_zero_divisors` sweep can never find a counterexample and `babybear8.rs::inverse`
   always succeeds on nonzero input. NON-VACUITY TOOTH: the BUG that was fixed — reusing the
   non-residue `11` made `11` a square (`(x^2)^2 = 11`), so the top layer `y^2 - 11 = (y-x^2)(y+x^2)`
   FACTORED and the quotient degenerated to the product ring `F × F`, which provably HAS a zero
   divisor (`(1,0)·(0,1) = 0`, neither factor zero, `(1,0)` not a unit) — the literal old witness
   `A = y - x^2`. So "no zero divisors" is TRUE for the genuine field and provably FALSE for the
   broken product-ring: the field property is not vacuous.

2. **"The generator has prime order N" (no Pohlig–Hellman shortcut).** EMPIRICAL SEED: `N` is a
   248-bit prime and `N·G = O`, `G ≠ O`, cofactor 1 (PARI `isprime(N)`, `ellcard(E)==N`; Rust
   `generator_has_order_n`, `generator_cofactor_is_one`). THEOREM (here): in ANY group, `g^N = 1` +
   `N` prime + `g ≠ 1` force `orderOf g = N` exactly — there is NO proper nontrivial subgroup for a
   Pohlig–Hellman descent to drop into. NON-VACUITY TOOTH: drop primality — the OLD placeholder order
   `2013191319 = 3·331·2027383` was composite, and a composite annihilator genuinely admits a proper
   subgroup (concrete witness over `ZMod 6`: `g = 2` has `g^6 = 1`, `g ≠ 1`, yet `orderOf g = 3 ≠ 6`).
   So the prime hypothesis is LOAD-BEARING, not decorative.

3. **"The AIR enforces s·G + e·pk == R".** The in-circuit verification relation as a first-class
   predicate `SchnorrVerifies`, with the soundness reduction (an accepting trace on a public `R'`
   pins `R' = s·G + e·pk`) and the FORGERY TOOTH mirroring `schnorr_air.rs`'s
   `forged_signature_with_bit_valid_trace_rejected`: a curve where the relation accepts a WRONG `R`
   exhibits a concrete forgery; the genuine relation rejects it. PLUS (§3a) the `smul` in that
   relation is not taken on faith: double-and-add (`daa`, the `fill_scan_phase` recursion) is PROVEN
   to compute `n·G` (`daa_correct` / `daa_from_origin`) — the structural content of
   `scan_computes_scalar_products`, with `daa_flip_lsb_changes` = `flipped_bit_breaks_transition`.

## What stays a typed crypto PRIMITIVE (named, never a Lean law, never `:= True`)

- `Nat.Prime p` for `p = 2^31 - 2^27 + 1` (BabyBear) and `Irreducible (z^8 - 11)` over `F_p` — finite
  checks (a known prime / PARI irreducibility). Carried as `Fact p.Prime` and `Fact (Irreducible f)`;
  given them, `ZMod.instField ⊳ AdjoinRoot.instField` makes the quotient a field, so pillar 1's
  theorem applies to the ACTUAL `BabyBear^8` tower (`babybear_tower_no_zero_divisors`), not just an
  abstract field.
- `N.Prime` and `#E = N` (= `N·G = O ∧ G ≠ O ∧ cofactor 1`) — PARI SEA point count. Carried as
  hypotheses; given them, pillar 2's theorem pins `ord(G) = N`.
- **DL hardness** on this curve (`SchnorrDLHard` below) — the bottom of the stack, like
  `Ed25519EufCma`. NOT proved, NOT `:= True`; a `Prop` carrier whose negation is a concrete DL
  solver. EUF of the Schnorr scheme reduces to it (forking lemma) — out of scope; we name it and pin
  the structure beneath it.

`#assert_axioms`-clean (⊆ `{propext, Classical.choice, Quot.sound}`). The empirical seeds enter as typeclass instances / hypotheses, not
`axiom`-keyword declarations, so they do not trip the hygiene guard — by design.
-/
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Abel
import Dregg2.Tactics

namespace Dregg2.Crypto.SchnorrCurveField

universe u

/-! ## §1 — Pillar 1: the field has no zero divisors.

The Rust `babybear8.rs::is_a_field_no_zero_divisors` sweeps a large family of nonzero elements and
asserts each is invertible (and that the old zero-divisor `A = y - x^2` is now invertible with
`A·(y+x^2) ≠ 0`). That is an empirical sample of a property which, for a GENUINE field, is a theorem:
nonzero ⇒ unit, and a product of nonzeros is nonzero. We prove the theorem (so no sample can ever
fail) and then exhibit the contrasting BROKEN ring to show the property is non-vacuous. -/

/-- **THEOREM (pillar 1, soundness side).** In any field, every nonzero element is a unit. This is
the abstract content the Rust `is_a_field_no_zero_divisors` sweep checks one sample at a time: the
sweep cannot find a non-invertible nonzero element because there is none. -/
theorem field_nonzero_isUnit {F : Type u} [Field F] {a : F} (ha : a ≠ 0) : IsUnit a :=
  ha.isUnit

/-- **THEOREM (pillar 1).** A field has NO zero divisors: a product of two nonzero elements is
nonzero. (The "no zero divisors" half of `is_a_field_no_zero_divisors`.) -/
theorem field_no_zero_divisors {F : Type u} [Field F] {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) :
    a * b ≠ 0 :=
  mul_ne_zero ha hb

/-- **THEOREM (pillar 1, applied to the ACTUAL tower).** Given the EMPIRICAL primitive that the
defining polynomial `f` is irreducible over the base field `F` (`z^8 - 11` over `F_p`, PARI-verified),
the quotient `F[z]/(f) = AdjoinRoot f` IS a field — `mathlib`'s `AdjoinRoot.instField` — so it has no
zero divisors. This is what makes `BabyBear^8` a genuine field rather than the old product ring. -/
theorem adjoinRoot_no_zero_divisors {F : Type u} [Field F] (f : Polynomial F)
    [Fact (Irreducible f)] {a b : AdjoinRoot f} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 :=
  -- `AdjoinRoot.instField` provides the `Field (AdjoinRoot f)` instance from `Fact (Irreducible f)`.
  mul_ne_zero ha hb

/-! ### Grounding pillar 1 in the ACTUAL base field `ZMod p` (BabyBear).

`adjoinRoot_no_zero_divisors` above is abstract over any `[Field F]`. The Rust tower is concrete:
the base is BabyBear `= ZMod p` with `p = 2^31 - 2^27 + 1 = 2013265921`, and the FIELD structure on
`ZMod p` is itself a consequence of `p` being PRIME (`ZMod.instField` needs `Fact p.Prime`). So the
full chain is: `Fact p.Prime` (finite primality check — a known prime, also a PARI fact) ⇒ `ZMod p` is
a field; `Fact (Irreducible (z^8 - 11))` (PARI) ⇒ `AdjoinRoot f` over THAT field is a field; hence no
zero divisors. We state pillar 1 over the real base-field TYPE `ZMod p`, threading BOTH empirical
seeds, so the theorem is about BabyBear^8 itself, not an abstract `F`. -/

/-- **THEOREM (pillar 1, the REAL tower).** With `p` prime — giving `ZMod p` (BabyBear) its field
structure — and the degree-8 defining polynomial `f` irreducible, the quotient
`(ZMod p)[X]/(f) = AdjoinRoot f` (= `BabyBear^8`) has NO zero divisors. Both hypotheses are the finite
empirical seeds (`p` prime; `f` irreducible — PARI), carried as `Fact`s; everything else is proved. -/
theorem babybear_tower_no_zero_divisors (p : ℕ) [Fact p.Prime] (f : Polynomial (ZMod p))
    [Fact (Irreducible f)] {a b : AdjoinRoot f} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 :=
  -- `ZMod.instField` (from `Fact p.Prime`) ⊳ `AdjoinRoot.instField` (from `Fact (Irreducible f)`).
  mul_ne_zero ha hb

/-- **THEOREM (pillar 1, the REAL tower — units).** Over the same real BabyBear tower, every nonzero
element is a unit (invertible) — the exact property `babybear8.rs::inverse` realizes and
`is_a_field_no_zero_divisors` samples. The Rust Gaussian-elimination inverse is the executable witness
of this existential. -/
theorem babybear_tower_nonzero_isUnit (p : ℕ) [Fact p.Prime] (f : Polynomial (ZMod p))
    [Fact (Irreducible f)] {a : AdjoinRoot f} (ha : a ≠ 0) : IsUnit a :=
  ha.isUnit

/-! ### Non-vacuity tooth (pillar 1): the BROKEN tower had a zero divisor.

The old construction reused the non-residue `11` at the top layer. Because `11 = (x^2)^2` is already
a square in `F_p[x]/(x^4 - 11)`, the polynomial `y^2 - 11 = (y - x^2)(y + x^2)` factored, and (CRT)
the quotient was the PRODUCT ring `F_{p^4} × F_{p^4}`. We model that product ring as `F × F` and
exhibit the literal zero divisor: `(1,0)` and `(0,1)` are both nonzero, but `(1,0)·(0,1) = (0,0)`,
and `(1,0)` is NOT a unit. This is `A = y - x^2` made concrete — the witness that is GONE in the
genuine field of pillar 1. -/

/-- The image of `A = y - x^2` in the broken product ring: the idempotent `(1, 0)`. (In the CRT
factor picture, `y - x^2` lands in one factor and vanishes in the other.) -/
def brokenA (F : Type u) [Field F] : F × F := (1, 0)

/-- The image of `y + x^2`: the complementary idempotent `(0, 1)`. -/
def brokenB (F : Type u) [Field F] : F × F := (0, 1)

/-- **TOOTH (pillar 1.a).** In the broken product ring, `A = (1,0)` is NONZERO… -/
theorem brokenA_ne_zero {F : Type u} [Field F] : brokenA F ≠ 0 := by
  intro h
  -- `(1,0) = 0` forces the first component `1 = 0` in the field — impossible.
  rw [brokenA, Prod.ext_iff] at h
  exact one_ne_zero h.1

/-- **TOOTH (pillar 1.b).** …and `y + x^2 = (0,1)` is NONZERO… -/
theorem brokenB_ne_zero {F : Type u} [Field F] : brokenB F ≠ 0 := by
  intro h
  rw [brokenB, Prod.ext_iff] at h
  exact one_ne_zero h.2

/-- **TOOTH (pillar 1.c) — THE ZERO DIVISOR.** …yet `A · (y + x^2) = (1,0)·(0,1) = (0,0) = 0`. Two
nonzero elements whose product is zero: the broken ring is NOT a domain. This is exactly the old
`A·(y+x^2) = 0` that `is_a_field_no_zero_divisors` now refutes for the real field. -/
theorem brokenA_mul_brokenB_eq_zero {F : Type u} [Field F] :
    brokenA F * brokenB F = 0 := by
  rw [brokenA, brokenB, Prod.ext_iff]
  exact ⟨by simp, by simp⟩

/-- **TOOTH (pillar 1.d).** And `A = (1,0)` has NO inverse in the product ring: a unit of `F × F` is
componentwise a unit (`Prod.isUnit_iff`), but the second component here is `0`, which is never a unit
in a field. So the broken ring fails `field_nonzero_isUnit` on a nonzero element — the precise failure
the rebuild removed. -/
theorem brokenA_not_isUnit {F : Type u} [Field F] : ¬ IsUnit (brokenA F) := by
  rw [brokenA, Prod.isUnit_iff]
  -- a unit in `F × F` needs both components units; the second is `0`, not a unit.
  rintro ⟨-, h0⟩
  exact not_isUnit_zero h0

/-- **TOOTH (pillar 1, headline).** The two facts side by side: the genuine field has no zero
divisor among `brokenA`-shaped nonzeros (vacuously — there is no zero divisor at all), while the
product ring exhibits one. Packaged as: in `F × F`, two nonzero elements multiply to zero — a
`NoZeroDivisors`-FALSE witness, so pillar 1's `field_no_zero_divisors` is non-vacuous (it genuinely
distinguishes the field from the broken ring). -/
theorem product_ring_has_zero_divisor {F : Type u} [Field F] :
    ∃ a b : F × F, a ≠ 0 ∧ b ≠ 0 ∧ a * b = 0 :=
  ⟨brokenA F, brokenB F, brokenA_ne_zero, brokenB_ne_zero, brokenA_mul_brokenB_eq_zero⟩

/-! ## §2 — Pillar 2: the generator has prime order N (no Pohlig–Hellman shortcut).

The Rust `schnorr_curve.rs::generator_has_order_n` asserts `N·G = O`; `generator_cofactor_is_one`
asserts `2·G ≠ O` (and small multiples non-identity); PARI asserts `isprime(N)` and cofactor 1. The
INFERENCE those tests stand for — "order divides the prime N and isn't 1, therefore order = N, so the
DL group has no proper nontrivial subgroup for Pohlig–Hellman" — is pure group theory, currently
living only in a Rust comment. We prove it abstractly over any group: `g^N = 1` (multiplicative form
of `N·G = O`), `N` prime, `g ≠ 1` ⇒ `orderOf g = N`. -/

/-- **THEOREM (pillar 2, soundness side).** In any monoid, if `g^N = 1` with `N` prime and `g ≠ 1`,
then `orderOf g = N`. The order divides the prime annihilator (so is `1` or `N`); it is not `1`
because `g ≠ 1`; hence it is exactly the prime `N`. Cofactor 1 / no Pohlig–Hellman subgroup is the
content: the only subgroup orders are `1` and `N`. -/
theorem orderOf_eq_of_prime_pow_eq_one {G : Type u} [Monoid G] {g : G} {N : ℕ}
    (hN : N.Prime) (hpow : g ^ N = 1) (hg : g ≠ 1) : orderOf g = N := by
  -- order divides the annihilator N
  have hdvd : orderOf g ∣ N := orderOf_dvd_of_pow_eq_one hpow
  -- a prime's only divisors are 1 and itself
  rcases (hN.eq_one_or_self_of_dvd _ hdvd) with h1 | hN'
  · -- orderOf g = 1 ⇒ g = 1, contradicting hg
    exact absurd (orderOf_eq_one_iff.mp h1) hg
  · exact hN'

/-- **THEOREM (pillar 2, corollary — the cofactor-1 / generation fact).** Under the same hypotheses
the order is at least 2 (`> 1`): no small-subgroup collapse. This is the abstract form of
`generator_cofactor_is_one`'s "no small multiple hits infinity". -/
theorem one_lt_orderOf_of_prime {G : Type u} [Monoid G] {g : G} {N : ℕ}
    (hN : N.Prime) (hpow : g ^ N = 1) (hg : g ≠ 1) : 1 < orderOf g := by
  rw [orderOf_eq_of_prime_pow_eq_one hN hpow hg]
  exact hN.one_lt

/-! ### Non-vacuity tooth (pillar 2): a COMPOSITE annihilator admits a proper subgroup.

The old placeholder generator `(1,2)` lived in the base-field embedding and had the COMPOSITE order
`2013191319 = 3·331·2027383` — trivially Pohlig–Hellman/Pollard-rho broken. The fix was to require a
PRIME order. To prove that hypothesis is load-bearing (not a decorative annotation), we exhibit a
concrete element with a COMPOSITE annihilator `n` that ALSO has a strictly SMALLER positive
annihilator `m` (`0 < m < n`, `m • x = 0`) — i.e. it sits in a PROPER nontrivial subgroup, the exact
Pohlig–Hellman drop a prime order forbids. So with a composite `n`, `n • x = 0 ∧ x ≠ 0` does NOT pin
the order to `n`; `orderOf_eq_of_prime_pow_eq_one`'s conclusion genuinely needs primality. -/

/-- **TOOTH (pillar 2) — primality is load-bearing.** A concrete element with a COMPOSITE annihilator
that drops into a proper subgroup: in additive `ZMod 6`, `x = 2` has `6 • x = 0` (composite
annihilator) and `x ≠ 0`, yet ALSO `3 • x = 0` with `0 < 3 < 6` — a strictly smaller positive
annihilator, so its true order is `< 6`. Were the curve order composite (the old `3·331·2027383`),
`N·G = O ∧ G ≠ O` would likewise FAIL to pin `ord(G) = N`; the prime hypothesis cannot be dropped.
(The smaller annihilator IS the Pohlig–Hellman subgroup the prime order eliminates.) -/
theorem composite_annihilator_proper_suborder :
    ∃ (n m : ℕ) (x : ZMod 6),
      ¬ n.Prime ∧ n • x = 0 ∧ x ≠ 0 ∧ 0 < m ∧ m < n ∧ m • x = 0 := by
  refine ⟨6, 3, (2 : ZMod 6), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- 6 is not prime
    decide
  · -- 6 • 2 = 0 in ZMod 6
    decide
  · -- 2 ≠ 0 in ZMod 6
    decide
  · -- 0 < 3
    decide
  · -- 3 < 6
    decide
  · -- 3 • 2 = 0 in ZMod 6: the proper-subgroup (Pohlig–Hellman) drop
    decide

/-! ## §3 — Pillar 3: the AIR enforces the Schnorr verification relation `s·G + e·pk == R`.

The RETIRED `schnorr_air.rs::check_trace_constraints` (see the retirement note at the top — deleted as
dead pre-law algebra) witnessed `s·G` and `e·pk` via double-and-add with a final boundary asserting
`s·G + e·pk == R`. The soundness-relevant content this file formalizes ABSTRACTLY is: an accepting trace
on public `R'` PINS `R' = s·G + e·pk`. This is now the specification a FUTURE Lean-EMITTED value-path
signature circuit must satisfy, not a mirror of deployed Rust. We state the verification relation as a first-class predicate over
an abstract additive group of curve points (the group law is mathlib's `AddCommGroup`; the curve's
specific `add`/`double` are the Rust executable model, exercised by `scan_computes_scalar_products`),
parameterised by a `ScalarMul` action giving `s·G`. The forgery tooth mirrors
`forged_signature_with_bit_valid_trace_rejected`. -/

/-- A curve-point group equipped with the scalar action the AIR computes: `smul s P = s·P` realised
by double-and-add. We abstract over the concrete curve so the relation is about the verification
EQUATION, not the field arithmetic (which is the Rust model + pillars 1–2). -/
structure CurveGroup where
  /-- The abelian group of points (the curve group; `O` is `0`). -/
  Pt : Type u
  [grp : AddCommGroup Pt]
  /-- Scalar multiplication `s • P = s·P` (double-and-add in `schnorr_curve.rs`). -/
  smul : ℕ → Pt → Pt

attribute [instance] CurveGroup.grp

/-- **`SchnorrVerifies C G pk s e R`** — the in-circuit verification relation: the boundary equation
`s·G + e·pk == R` that `check_trace_constraints` enforces, with `G` the fixed generator, `pk` the
public key, `s` the response scalar, `e` the Fiat–Shamir challenge, `R` the public nonce point. -/
def SchnorrVerifies (C : CurveGroup) (G pk : C.Pt) (s e : ℕ) (R : C.Pt) : Prop :=
  C.smul s G + C.smul e pk = R

/-- **THEOREM (pillar 3, soundness reduction).** An accepting trace PINS `R`: if the relation holds
for public `R`, then `R` is exactly `s·G + e·pk`. This is the extraction the AIR gives — the verifier
learns the boundary value, nothing weaker. (Trivial by definition, but it is the statement the
forgery tooth refutes for a wrong `R`.) -/
theorem schnorr_pins_R {C : CurveGroup} {G pk : C.Pt} {s e : ℕ} {R : C.Pt}
    (h : SchnorrVerifies C G pk s e R) : R = C.smul s G + C.smul e pk :=
  h.symm

/-- **THEOREM (pillar 3) — a wrong `R` cannot verify the same `(s,e)`.** If `R ≠ s·G + e·pk` then the
relation does NOT hold for that `R`. This is the abstract content of the forgery tooth: forging the
public `R` (to `2G`, as in `schnorr_air.rs`) while keeping the witnessed `s·G`/`e·pk` breaks the
boundary equality. -/
theorem schnorr_rejects_wrong_R {C : CurveGroup} {G pk : C.Pt} {s e : ℕ} {R : C.Pt}
    (hne : R ≠ C.smul s G + C.smul e pk) : ¬ SchnorrVerifies C G pk s e R :=
  fun h => hne (schnorr_pins_R h)

/-! ### §3a — the double-and-add scan REALIZES the scalar action (closing the `smul` gap).

`SchnorrVerifies` takes `C.smul` (= `s·P`) as given. But the AIR does NOT take `s·G` on faith: each
scan phase WITNESSES it by double-and-add over the scalar's bits, and the transition constraints
(`flipped_bit_breaks_transition`, `corrupted_lambda_rejected`, `scan_computes_scalar_products`) force
the witnessed accumulator to be the genuine scalar product. Abstracting `smul` as opaque hides exactly
this. Here we model double-and-add as the concrete recursion `daa` (the `schnorr_air.rs::fill_scan_phase`
loop: read bits LSB→MSB, accumulate on a set bit, double the base each step) and PROVE it computes
`n • G` — so the value the boundary equation compares is the real scalar multiple, not an assumption.
This is the structural content of `scan_computes_scalar_products`; `daa_flip_lsb` is
`flipped_bit_breaks_transition`. -/

/-- The value of an LSB-first bit list as a natural number — the scalar the scan realizes. -/
def bitsVal : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * bitsVal bs

/-- **Double-and-add**, the exact `fill_scan_phase` computation over an additive group: fold the bit
list LSB-first, accumulating `base` on a set bit and doubling `base` each step. `acc` is the running
accumulator (the trace's `ACC` column), `base` the running `2^i·G` (the `BASE` column). -/
def daa {G : Type u} [AddCommGroup G] : List Bool → G → G → G
  | [], acc, _ => acc
  | b :: bs, acc, base => daa bs (if b then acc + base else acc) (base + base)

/-- One scan step (unfolds `daa` on a cons) — the per-row transition `schnorr_air.rs` checks. -/
theorem daa_cons {G : Type u} [AddCommGroup G] (b : Bool) (bs : List Bool) (acc base : G) :
    daa (b :: bs) acc base = daa bs (if b then acc + base else acc) (base + base) := rfl

/-- **THEOREM (pillar 3a, scan correctness).** Double-and-add over a bit list, from running
accumulator `acc` and running base `base`, yields `acc + (value of the bits)·base`. Proven by
induction generalizing the running base (= `2^k·G`) and accumulator — the loop invariant the AIR's
accumulator/base transitions encode. -/
theorem daa_correct {G : Type u} [AddCommGroup G] (bs : List Bool) (acc base : G) :
    daa bs acc base = acc + (bitsVal bs) • base := by
  induction bs generalizing acc base with
  | nil => simp [daa, bitsVal]
  | cons b bs ih =>
    rw [daa_cons, ih, bitsVal]
    have hb : base + base = (2 : ℕ) • base := (two_smul ℕ base).symm
    rw [hb, smul_smul, add_smul, Nat.mul_comm]
    cases b with
    | false => simp only [Bool.false_eq_true, if_false, zero_smul, zero_add]
    | true =>
      simp only [if_true, one_smul]
      abel

/-- **THEOREM (pillar 3a, headline).** Run from the AIR's boundary start (`acc = O = 0`, `base = G`),
the scan computes exactly `(bitsVal bits)·G` — i.e. the scalar multiple `s·G`. So the `C.smul s G` in
`SchnorrVerifies` is not an unexamined input: it is the proven output of the witnessed double-and-add,
which is what `scan_computes_scalar_products` asserts (`phase-0 final accumulator == s·G`). -/
theorem daa_from_origin {G : Type u} [AddCommGroup G] (g : G) (bs : List Bool) :
    daa bs (0 : G) g = (bitsVal bs) • g := by
  rw [daa_correct]; abel

/-! #### Non-vacuity tooth (pillar 3a): scan-correctness genuinely DISCRIMINATES.

Over `ℤ` with base `1`, the scan computes the integer the bits denote: `[true,false,true]` (LSB-first
binary `101 = 5`) yields `5`. FLIPPING the low bit to `[false,false,true]` (`100 = 4`) changes the
result — so the accumulator is NOT bit-independent; a tampered bit yields a different scalar product,
exactly `flipped_bit_breaks_transition`. -/

/-- (accept) The scan over `[true,false,true]` (= 5, LSB-first) from `0` with base `1` gives `5`. -/
theorem daa_realizes_five : daa [true, false, true] (0 : ℤ) 1 = 5 := by decide

/-- (reject / tooth) Flipping the LOW bit (`[true,…] → [false,…]`) changes the scan output — the
accumulator depends on every bit, so a stale/flipped bit produces a wrong scalar product. Mirror of
`schnorr_air.rs::flipped_bit_breaks_transition`. -/
theorem daa_flip_lsb_changes :
    daa [false, false, true] (0 : ℤ) 1 ≠ daa [true, false, true] (0 : ℤ) 1 := by decide

/-! ### Non-vacuity tooth (pillar 3): the relation is TRUE and FALSE on a concrete curve.

We instantiate `CurveGroup` with the integers under addition and `smul := (· * ·)` (a faithful toy
scalar action: `s • G = s * G`). The relation `s·G + e·pk = R` then both HOLDS (on the honestly
computed `R = sG + e·pk`) and FAILS (on a forged `R'`), proving `SchnorrVerifies` is non-vacuous —
exactly `valid_signature_trace_accepted` vs `forged_signature_with_bit_valid_trace_rejected`. -/

/-- A concrete toy curve group: `ℤ` under `+`, scalar action `s • g = s * g`. -/
def toyCurve : CurveGroup where
  Pt := ℤ
  smul := fun s g => (s : ℤ) * g

/-- (a) ACCEPT — on the honestly computed boundary value the relation HOLDS. With `G = pk = 1`,
`s = 3`, `e = 5`, the honest `R = 3·1 + 5·1 = 8` verifies. (Mirror of `valid_signature_trace`.) -/
theorem toy_verifies_honest : SchnorrVerifies toyCurve (1 : ℤ) (1 : ℤ) 3 5 (8 : ℤ) := by
  -- 3 • 1 + 5 • 1 = 3*1 + 5*1 = 8
  show (3 : ℤ) * 1 + (5 : ℤ) * 1 = 8
  decide

/-- (b) REJECT — a FORGED `R' = 9 ≠ 8` does NOT verify the same `(s, e)`. The honest boundary is `8`;
swapping in any other `R'` breaks it. (Mirror of `forged_signature_with_bit_valid_trace_rejected`:
forge `R` and the final equality fails.) -/
theorem toy_rejects_forged : ¬ SchnorrVerifies toyCurve (1 : ℤ) (1 : ℤ) 3 5 (9 : ℤ) := by
  apply schnorr_rejects_wrong_R
  -- 9 ≠ 3*1 + 5*1 = 8
  show (9 : ℤ) ≠ (3 : ℤ) * 1 + (5 : ℤ) * 1
  decide

/-! ## §4 — The bottom of the stack: DL hardness as a typed PRIMITIVE.

Like `Ed25519Reduction.Ed25519EufCma`, the discrete-log assumption on THIS curve is the irreducible
cryptographic hypothesis. It is NOT a Lean theorem and NOT `:= True`; it is a `Prop` carrier with
explicit content — its negation is a concrete DL solver (an algorithm that, given `pk = sk·G`,
recovers `sk`). Pillars 1–2 are exactly the STRUCTURE this assumption needs to be plausible (a real
field, a prime-order group with no Pohlig–Hellman shortcut); the assumption itself is named here and
left as the standing obligation. Schnorr EUF reduces to it via the forking lemma (out of scope). -/

/-- **`DLSolver C G`** — the discrete-log adversary's WIN: a function recovering the scalar from the
point, i.e. for every secret `sk`, given `sk·G` it returns `sk`. Its EXISTENCE breaks DL. -/
def DLSolver (C : CurveGroup) (G : C.Pt) : Prop :=
  ∃ solve : C.Pt → ℕ, ∀ sk : ℕ, solve (C.smul sk G) = sk

/-- ⚠ **DEGENERATE AT FINITE PARAMETERS — an EXISTENCE-REFUTATION whose truth tracks a modelling artifact,
not hardness.** `DLSolver` demands a `solve` with `solve (sk·G) = sk` for ALL `sk : ℕ`. On any FINITE point
group `sk ↦ sk·G` is non-injective, so no such `solve` can exist and `SchnorrDLHard` is TRIVIALLY TRUE —
satisfied by the addition group, by a broken curve, by anything finite, with ZERO cryptographic content. The
FALSIFIABILITY TOOTH `CryptoFloorTeeth.schnorrDLHard_of_smul_collision` proves it holds from ANY `sk`-collision
(fires on the finite `ZMod 5` toy). The opposite pole `toy_dl_not_hard` REFUTES it on the INFINITE toy, where
`sk ↦ sk` is injective — so this predicate discriminates on injectivity-over-`ℕ`, not on DL hardness. The
proper floor is the advantage-based `SchnorrEufCma.SchnorrDLHardF` / `ProbSchnorrFamily` (a noticeable-advantage
adversary), never this existence check — see `CryptoFloorTeeth`. -/
def SchnorrDLHard (C : CurveGroup) (G : C.Pt) : Prop :=
  ¬ DLSolver C G

/-- The primitive has explicit content: it is exactly the negation of "a DL solver exists" — a
forger is a concrete refutation, not an opaque token. (Definitional; pins the framing, the way
`Ed25519Reduction.eufCma_iff_sound` does for ed25519.) -/
theorem dlHard_iff_no_solver {C : CurveGroup} {G : C.Pt} :
    SchnorrDLHard C G ↔ ¬ DLSolver C G := Iff.rfl

/-- **Non-vacuity of the primitive (the broken direction).** On a DEGENERATE curve where the scalar
action is injective-with-known-inverse, DL is provably EASY: a solver exists, so `SchnorrDLHard` is
FALSE. Concretely on `toyCurve` with `G = 1`, `s • 1 = s`, so `solve := Int.toNat` recovers every
`sk` and `SchnorrDLHard` fails. This proves the primitive is a REAL discriminating assumption (it can
be false), not a vacuous `True`. The real curve (prime order, ~124-bit) is conjectured to satisfy it;
the toy curve provably does not. -/
theorem toy_dl_not_hard : ¬ SchnorrDLHard toyCurve (1 : ℤ) := by
  -- solve x = x.toNat recovers sk from sk • 1 = sk*1 = sk (a nonneg integer).
  refine fun h => h ⟨fun (x : ℤ) => x.toNat, fun sk => ?_⟩
  show ((sk : ℤ) * 1).toNat = sk
  simp

/-! ## §5 — Axiom-hygiene tripwires. Every keystone pins exactly the kernel-clean whitelist
`{propext, Classical.choice, Quot.sound}`. The standing obligations are the NAMED typed primitives —
`Fact (Irreducible (z^8-11))` and `N.Prime` (finite checks, PARI), and `SchnorrDLHard` (the curve DL
assumption). -/

#assert_all_clean [
  field_nonzero_isUnit,
  field_no_zero_divisors,
  adjoinRoot_no_zero_divisors,
  babybear_tower_no_zero_divisors,
  babybear_tower_nonzero_isUnit,
  brokenA_ne_zero,
  brokenB_ne_zero,
  brokenA_mul_brokenB_eq_zero,
  brokenA_not_isUnit,
  product_ring_has_zero_divisor,
  orderOf_eq_of_prime_pow_eq_one,
  one_lt_orderOf_of_prime,
  composite_annihilator_proper_suborder,
  schnorr_pins_R,
  schnorr_rejects_wrong_R,
  daa_cons,
  daa_correct,
  daa_from_origin,
  daa_realizes_five,
  daa_flip_lsb_changes,
  toy_verifies_honest,
  toy_rejects_forged,
  dlHard_iff_no_solver,
  toy_dl_not_hard
]

end Dregg2.Crypto.SchnorrCurveField

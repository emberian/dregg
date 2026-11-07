import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum.Prime
import Dregg2.Circuit.FriSoundness

/-!
# DEBT-A brick 1 — BabyBear is a field that satisfies the FRI-soundness requirements

The census / DEBT-A worry was "`ZMod 5` ≠ BabyBear" — the field-generic FRI soundness
(`FriSoundness.fold_close_of_two_alpha`, `friProximity_discharge`) was only ever *instantiated* at a
`ZMod 5` demo field. But those lemmas require ONLY `[Field F] [DecidableEq F]` (`FriSoundness.lean:69`) —
no generator, no field-specific structure. So the swap to the DEPLOYED field is a clean instantiation, not
new theory. This file makes that concrete:

- **BabyBear** `p = 2³¹ − 2²⁷ + 1 = 2013265921` (`circuit/src/field.rs`, the descriptor's `field_modulus`).
- `p` is **prime** ⇒ `ZMod p` is a `Field` with `DecidableEq` — exactly what the FRI lemmas need.
- `p − 1 = 2013265920 = 15·2²⁷` ⇒ **2-adicity is EXACTLY 27**: BabyBear has the smooth power-of-two
  subgroups FRI folds over (and no more — the smoothness is precisely 2²⁷, the deployed FRI domain cap).

SCOPE (honest): this establishes BabyBear as a FIELD that meets the FRI lemmas' typeclass requirements — the
field-swap the census flagged as missing. The downstream bricks are now DONE: `BabyBearFriSetup.lean` (brick 2)
constructs the BabyBear `FriGeom`/`FriSetup` and `BabyBearFriDeployed.lean` (brick 3) parameterizes it over the
size-`2^(m+1)` domain, instantiating at the deployed rate `1/8` (`m=3`) and the full `2²⁷` 2-adicity cap
(`m=26`). `BabyBearFriDeployedInstance.lean` binds the floor at the deployed WRAP config (rate `1/64`,
`numQueries=19`): the setup, the payoff lemmas, the `19`-query reject teeth (DISCHARGED), and the honest
residual `FriLdtDeployedBound` (the BCIKS20 Johnson-radius list-decoding assumption, NAMED not faked — the one
research-grade floor). Residual so far in THIS brick: none (`norm_num`/typeclass facts only).
-/

namespace Dregg2.Circuit.BabyBearFriField

/-- **The BabyBear prime** `2³¹ − 2²⁷ + 1` — the deployed prover's field (`field_modulus: 2013265921`
in the v2 descriptor, `DescriptorIR2.lean:1521`). -/
abbrev babyBearP : ℕ := 2013265921

set_option maxRecDepth 8192 in
/-- **BabyBear is prime.** (`norm_num`'s Pratt-certificate primality extension.) -/
theorem babyBearP_prime : Nat.Prime babyBearP := by norm_num

instance instFactBabyBearPrime : Fact (Nat.Prime babyBearP) := ⟨babyBearP_prime⟩

/-- **BabyBear** as a Lean field: `ZMod p` for the prime `p`. -/
abbrev BabyBear := ZMod babyBearP

/-- BabyBear is a `Field` — the first typeclass `fold_close_of_two_alpha` requires.
NOTE (2026-07-12): `ZMod p` (prime) IS computable in principle (inverse via extended-Euclid), and a
plain `instance : Field BabyBear := inferInstance` typechecks WITHOUT `noncomputable`. BUT making it
globally computable forces Lean to CODE-GENERATE the entire BabyBear-valued def tree (the huge
descriptors / constraint lists / RotationV3+apex chain) on every build — measured 55GB+ per `lake
build` (ember killed several). So it is kept `noncomputable` for BUILD HYGIENE, not because the field
is intrinsically noncomputable. For concrete circuit EVALUATION (KATs, the wrap analyzer on real
values), use a TARGETED computable instance/copy on the small witness — never globally. -/
noncomputable instance : Field BabyBear := inferInstance

/-- BabyBear has `DecidableEq` — the second typeclass the FRI lemmas require. -/
instance : DecidableEq BabyBear := inferInstance

/-! ## 2-adicity — the FRI smoothness, both polarities. -/

/-- **BabyBear has 2-adicity ≥ 27**: `2²⁷ ∣ p − 1` (`p − 1 = 15·2²⁷`). FRI folds over the size-`2^k`
subgroups; BabyBear supplies them up to `k = 27`. -/
theorem babyBear_two_adicity_ge_27 : (2 ^ 27 : ℕ) ∣ (babyBearP - 1) := by norm_num

/-- **…and EXACTLY 27** (both-truth tooth): `2²⁸ ∤ p − 1`. The smoothness is precisely `2²⁷` — the deployed
FRI evaluation-domain size cap, not an over-claim. -/
theorem babyBear_two_adicity_lt_28 : ¬ (2 ^ 28 : ℕ) ∣ (babyBearP - 1) := by norm_num

/-! ## The payoff: BabyBear meets the FRI-lemma typeclass requirements.

`fold_close_of_two_alpha` / `friProximity_discharge` are stated over `variable {F : Type*} [Field F]
[DecidableEq F]` (`FriSoundness.lean:69`). BabyBear provides both instances (above), so the field-generic
BBHR18 reconstruction applies at `F := BabyBear` with NO extra field theory — the "field-swap" the census
flagged as missing is a typeclass instantiation. `debtA_babybear_meets_fri_requirements` records exactly that
(both instances inhabited); actually instantiating `fold_close_of_two_alpha` at a BabyBear `FriSetup` is DEBT-A
brick 2 (construct the BabyBear evaluation domain from the 2²⁷ subgroup + bind to the deployed FRI config). -/

/-- **BabyBear satisfies the FRI lemmas' requirements** — `Field` and `DecidableEq`, the only two classes
`fold_close_of_two_alpha` needs. So the field-generic FRI soundness specializes to the deployed field. -/
theorem debtA_babybear_meets_fri_requirements :
    Nonempty (Field BabyBear) ∧ Nonempty (DecidableEq BabyBear) :=
  ⟨⟨inferInstance⟩, ⟨inferInstance⟩⟩

end Dregg2.Circuit.BabyBearFriField

import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Dregg2.Circuit.FriProximityGapWitness
import Dregg2.ForMathlib.GuruswamiSudan

/-!
# `WrapCorrelatedAgreementSharp` — the δ-PRESERVING (Johnson-radius) residual, REDUCED to the
BCIKS20 affine-line correlated-agreement primitive, and the primitive NAMED as a Lean `Prop`.

`FriProximityGapWitness.lean` pushed the Fisher/packing method to its exact ceiling:
`wrap_badChallengePoly_johnson` proves `BadChallengePoly friSetupWrapRate 112 42 26` — `L = 26` at
the Johnson OUTER radius `dOut = 112` but with `dIn = 42` (relative `21/32`), NOT the folded code's
own Johnson radius `dIn = 56` (relative `7/8`). The obstruction is arithmetic and sharp: the packing
quadratic `a² > n·M` (`a = 64 − dIn`, `n = 64`, `M = 7`) FAILS for `dIn ≥ 43` (`a ≤ 21`,
`a² ≤ 441 < 448`). So the packing radius is *dead* at `dIn = 56` (`a = 8`, `a² = 64 ≪ 448`):
farness degrades across the fold (`7/8 → 21/32`) rather than being δ-preserved (`7/8 → 7/8`).

That named residual is `WrapCorrelatedAgreementSharp L := BadChallengePoly friSetupWrapRate 112 56 L`
(`FriProximityGapWitness.lean §F`). This file does not fake it. It does two honest things.

## §1. The exact remaining primitive, NAMED (`CorrelatedAgreementLine`).

BCIKS20's *correlated agreement for an affine line* over a code `C'`: viewing the FRI fold
`Fold α f = E f + α·O f` as the affine line `{u + α·v}` (`u = E f`, `v = O f`) of functions on the
folded domain, if MORE than `L` challenges `α` fold `f` to within `dIn` of `C'`, then there is a
SINGLE common agreement — codewords `ge, go ∈ C'` and a set of fibers `S` with
`|S| ≥ |κ| − dIn` on which `E f = ge` and `O f = go` SIMULTANEOUSLY. The threshold `|κ| − dIn` is the
**δ-preserving** (relative `1 − δ`) agreement — the sharp BCIKS20 statement, beyond the packing reach.
`CorrelatedAgreementLineAt S dIn L agree` carries the agreement threshold as a parameter so the
δ-preserving version (`agree = |κ| − dIn`) and the two-point version (`agree = |κ| − 2·dIn`) share one
shape.

This primitive is NOT assumed anywhere in the deployed chain (which consumes
`wrap_friProximityGap_johnson`, a theorem). It is stated so the residual is a Lean `Prop`, not prose.

## §2. The REDUCTION (`sharp_of_correlatedAgreementLine`) — a THEOREM, no `sorry`.

`CorrelatedAgreementLine friSetupWrapRate 56 L → WrapCorrelatedAgreementSharp L`. The mechanism is
the deployed dimension-`2` collapse already proved in `FriProximityGapWitness.lean`: on the wrap
setup `C'` is the CONSTANTS, so the correlated-agreement codewords are `ge = const a`, `go = const b`,
and their common agreement set is EXACTLY `Φ⁻¹(a, b) = {y | E f y = a ∧ O f y = b}`. δ-preservation
forces `|Φ⁻¹(a,b)| ≥ 64 − 56 = 8`, but `far_fiber_card` / `wrap_fiber_le_seven` cap it at
`(128 − 112 − 1)/2 = 7` for a `112`-far word. `8 ≤ 7` is absurd, so the good set has `≤ L` elements —
and the BCIKS20 witness polynomial `∏_{α good}(X − C α)` (nonzero, degree `≤ L`) is exhibited exactly
as in `wrap_badChallengePoly_johnson`. This is where the sharp `7/8 → 7/8` δ-preservation lives: the
one place `far_fiber_card`'s `M = 7` *beats* the `δ = 7/8` agreement floor of `8`.

## §3. Non-vacuity / genuine-strengthening certificate (`correlatedAgreementLineAt_twoPoint`).

The primitive is not a black box: at `L = 1` its WEAK form (`agree = |κ| − 2·dIn`) is a THEOREM,
proved by the BBHR18 two-point reconstruction (the same Vandermonde solve behind
`fold_close_of_two_alpha`): two good challenges pin `E f = Ge`, `O f = Go` off the union of the two
disagreement sets, giving common agreement on `≥ |κ| − 2·dIn` fibers with `Ge, Go ∈ C'`. So the
`∃ ge go, agree ≤ …` SHAPE is inhabited and provable; the SOLE gap to the sharp statement is the
strengthening of the agreement floor from `|κ| − 2·dIn` (two-point) to `|κ| − dIn` (δ-preserving) —
which is precisely BCIKS20's correlated-agreement content.

## ⚑ STATUS (2026-07-13) — §§3b/5/6/8 CLOSE the δ-preserving primitive by ORDERED-PAIR COUNTING.
What §3 leaves "open above" is subsequently PROVED (no `sorry`, no hypothesis) at the deployed list
sizes via the ordered-pair injection into `κ × κ` (card `4096`):
* `wrap_correlatedAgreement_sharp_proved : WrapCorrelatedAgreementSharp 292` — boundary radius
  `dIn = 56` (relative `7/8`), list `L = 292` (§3b/§5).
* `wrap_correlatedAgreementLine_interior : CorrelatedAgreementLine friSetupWrapRate 52 186` — the
  **interior** radius `dIn = 52` (relative `13/16`), list `L = 186`, GS-NON-DEGENERATE
  (`wrap_meets_gs_line_radius`: `t² = 144 > 128 = 2·|κ|`); the deployed analysis prefers this (§6).
* `wrap_perFold_soundness_capacity : |Good|/babyBearP⁴ < 2⁻¹¹²` — the near-capacity radius
  `dOut = 125`, field-independent count `|Good| ≤ C(64,2) = 2016`, the **arity-2 (2-to-1 fold)**
  **~112.6-bit** proven per-fold soundness over the quartic extension (§8). ⚠ This is NOT the deployed
  posture: the deployed prover folds at ARITY 8 and carries **~109.84 bits**
  (`FriArityTransfer.arity8_perFold_soundness`); ~112.6 provably FAILS at arity 8
  (`arity8_error_not_lt_2e112`). SOUND against Kambiré's capacity refutation:
  his `n^C` blow-up needs `n → ∞`, `r > 2`; at fixed `r = 2` his construction caps at `C(n,2)`.
The **GS-IDEAL list `L ≤ 2·|κ| = 128` is BLOCKED** for the constant-fold multiset word
(`Dregg2/ForMathlib/GuruswamiSudan.lean:20-33` is the authority — multiplicity/fibre-concentration
obstruction); `186`/`292` is the sharpest reach of the ordered-pair method, not the GS ideal.
Security is unaffected — the list term is `L/|F|` with `|F| ≈ 2¹²⁴`.

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; no `axiom`, no `sorry`.
-/

namespace Dregg2.Circuit.FriCorrelatedAgreementSharp

open Dregg2.Circuit.FriSoundness
open Dregg2.Circuit.FriLdtJohnson
open Dregg2.Circuit.FriProximityGapListDecoding
open Dregg2.Circuit.FriProximityGapWitness
open Dregg2.Circuit.BabyBearFriDeployed
open Dregg2.Circuit.BabyBearFriField (BabyBear babyBearP)
open Dregg2.Circuit.BabyBearFriDeployedInstance (friSetupWrapRate)
open Polynomial
open scoped BigOperators

variable {F : Type*} [Field F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-! ## §1. The named BCIKS20 affine-line correlated-agreement primitive. -/

/-- **BCIKS20 correlated agreement for the FRI affine line, at agreement floor `agree`.** If more
than `L` folding challenges `α` fold `f` to within `dIn` of the folded code `C'`, then a SINGLE pair
of folded codewords `ge, go ∈ C'` agrees with `(E f, O f)` on at least `agree` fibers SIMULTANEOUSLY.

The δ-preserving (sharp) instance is `agree = |κ| − dIn`; the two-point (unique-decoding) instance is
`agree = |κ| − 2·dIn` (`§3`). -/
def CorrelatedAgreementLineAt (S : FriSetup F ι κ) (dIn L agree : ℕ) : Prop :=
  ∀ {f : ι → F} (Good : Finset F),
    (∀ α ∈ Good, closeN S.C' dIn (Fold S.geom α f)) → L < Good.card →
    ∃ ge ∈ S.C', ∃ go ∈ S.C',
      agree ≤
        (Finset.univ.filter (fun y : κ => E S.geom f y = ge y ∧ O S.geom f y = go y)).card

/-- **The δ-PRESERVING correlated-agreement primitive** — the sharp BCIKS20 statement: the common
agreement set is of relative size `1 − δ` (`|κ| − dIn` fibers), matching the OUTER far-ness's relative
size. This is the exact content beyond the packing quadratic's `21/32` reach. -/
def CorrelatedAgreementLine (S : FriSetup F ι κ) (dIn L : ℕ) : Prop :=
  CorrelatedAgreementLineAt S dIn L (Fintype.card κ - dIn)

/-! ## §3 (stated first — the non-vacuity certificate). The two-point reconstruction gives the WEAK
agreement floor `|κ| − 2·dIn`, so the primitive's `∃ ge go, agree ≤ …` shape is inhabited. -/

/-- **Two good challenges reconstruct a common agreement set of `≥ |κ| − 2·dIn` fibers.** The BBHR18
Vandermonde solve (as in `fold_close_of_two_alpha`): off the union `T` of the two disagreement sets
(`|T| ≤ 2·dIn`), the fold equations `E f + αᵢ·O f = gᵢ` pin `E f = Ge`, `O f = Go`, with
`Ge, Go ∈ C'` the reconstructed folded codewords. So `Tᶜ` (of card `≥ |κ| − 2·dIn`) lies in the
common agreement set. -/
theorem correlatedAgreementLine_twoPoint (S : FriSetup F ι κ) {f : ι → F} {α₁ α₂ : F}
    (hα : α₁ ≠ α₂) {d : ℕ}
    (h1 : closeN S.C' d (Fold S.geom α₁ f)) (h2 : closeN S.C' d (Fold S.geom α₂ f)) :
    ∃ ge ∈ S.C', ∃ go ∈ S.C',
      Fintype.card κ - 2 * d ≤
        (Finset.univ.filter (fun y : κ => E S.geom f y = ge y ∧ O S.geom f y = go y)).card := by
  classical
  obtain ⟨g₁, hg₁, hc₁⟩ := h1
  obtain ⟨g₂, hg₂, hc₂⟩ := h2
  set G := S.geom with hG
  have hne : α₁ - α₂ ≠ 0 := sub_ne_zero.mpr hα
  set inv : F := (α₁ - α₂)⁻¹ with hinv
  set Go : κ → F := inv • (g₁ - g₂) with hGo
  set Ge : κ → F := inv • (α₁ • g₂ - α₂ • g₁) with hGe
  have hGoC : Go ∈ S.C' := S.C'.smul_mem _ (S.C'.sub_mem hg₁ hg₂)
  have hGeC : Ge ∈ S.C' :=
    S.C'.smul_mem _ (S.C'.sub_mem (S.C'.smul_mem _ hg₂) (S.C'.smul_mem _ hg₁))
  set T : Finset κ := disagree (Fold G α₁ f) g₁ ∪ disagree (Fold G α₂ f) g₂ with hT
  refine ⟨Ge, hGeC, Go, hGoC, ?_⟩
  -- `Tᶜ` lies in the common agreement set.
  have hkey : Tᶜ ⊆ Finset.univ.filter (fun y : κ => E G f y = Ge y ∧ O G f y = Go y) := by
    intro y hy
    rw [Finset.mem_compl, hT, Finset.mem_union, not_or] at hy
    obtain ⟨hy1, hy2⟩ := hy
    have e1 : E G f y + α₁ * O G f y = g₁ y := by
      have h := hy1; rw [mem_disagree, not_not] at h; simpa [Fold] using h
    have e2 : E G f y + α₂ * O G f y = g₂ y := by
      have h := hy2; rw [mem_disagree, not_not] at h; simpa [Fold] using h
    have hGoy : Go y = inv * (g₁ y - g₂ y) := by
      simp only [hGo, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    have hGey : Ge y = inv * (α₁ * g₂ y - α₂ * g₁ y) := by
      simp only [hGe, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · rw [hGey, hinv, inv_mul_eq_div, eq_div_iff hne]
      linear_combination α₁ * e2 - α₂ * e1
    · rw [hGoy, hinv, inv_mul_eq_div, eq_div_iff hne]
      linear_combination e1 - e2
  -- `|T| ≤ 2d`, so `|Tᶜ| = |κ| − |T| ≥ |κ| − 2d`, and the agreement set is even bigger.
  have hTcard : T.card ≤ 2 * d := by
    rw [hT]
    calc (disagree (Fold G α₁ f) g₁ ∪ disagree (Fold G α₂ f) g₂).card
        ≤ (disagree (Fold G α₁ f) g₁).card + (disagree (Fold G α₂ f) g₂).card :=
          Finset.card_union_le _ _
      _ ≤ 2 * d := by omega
  have hcompl : Tᶜ.card = Fintype.card κ - T.card := by rw [Finset.card_compl]
  calc Fintype.card κ - 2 * d
      ≤ Tᶜ.card := by rw [hcompl]; omega
    _ ≤ _ := Finset.card_le_card hkey

/-- **The primitive is inhabited at `L = 1` with the WEAK (two-point) agreement floor.** This
certifies the `∃ ge go, agree ≤ …` shape is provable — the sole gap to the sharp `CorrelatedAgreementLine`
is the strengthening of the floor from `|κ| − 2·dIn` to `|κ| − dIn`, i.e. exactly δ-PRESERVATION. -/
theorem correlatedAgreementLineAt_twoPoint (S : FriSetup F ι κ) (dIn : ℕ) :
    CorrelatedAgreementLineAt S dIn 1 (Fintype.card κ - 2 * dIn) := by
  intro f Good hGood hcard
  obtain ⟨α₁, hα₁, α₂, hα₂, hne⟩ := Finset.one_lt_card.mp hcard
  exact correlatedAgreementLine_twoPoint S hne (hGood α₁ hα₁) (hGood α₂ hα₂)

/-! ## §2. The REDUCTION: the δ-preserving primitive discharges `WrapCorrelatedAgreementSharp`. -/

/-- **The good-challenge card bound at the SHARP inner radius, from correlated agreement.** Given the
δ-preserving line-correlated-agreement primitive at `dIn = 56`, a `112`-far word has at most `L`
folding challenges whose fold is `56`-close to the constants. The contradiction is the deployed
dimension-`2` collapse: correlated agreement would force `≥ 8` fibers onto a single point `(a, b)` of
`F²`, but `wrap_fiber_le_seven` caps that at `7`. -/
theorem wrap_good_challenge_card_le_sharp {f : Fin (2 ^ 7) → BabyBear} {L : ℕ}
    (hCA : CorrelatedAgreementLine friSetupWrapRate 56 L)
    (hfar : farN friSetupWrapRate.C 112 f)
    (Good : Finset BabyBear)
    (hGood : ∀ α ∈ Good, closeN friSetupWrapRate.C' 56 (Fold friSetupWrapRate.geom α f)) :
    Good.card ≤ L := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨ge, hge, go, hgo, hbig⟩ := hCA Good hGood hcon
  obtain ⟨a, rfl⟩ := mem_wrap_C'.mp hge
  obtain ⟨b, rfl⟩ := mem_wrap_C'.mp hgo
  have hle7 := wrap_fiber_le_seven hfar a b
  have hn : Fintype.card (Fin (2 ^ 6)) = 64 := by simp
  -- `hbig : |κ| − 56 ≤ |Φ⁻¹(a,b)|`; beta-reduce the constants `(fun _ => a) y ↦ a`.
  simp only at hbig
  rw [hn] at hbig
  omega

/-- **THE REDUCTION — `WrapCorrelatedAgreementSharp L` from the BCIKS20 line primitive.**
`CorrelatedAgreementLine friSetupWrapRate 56 L → BadChallengePoly friSetupWrapRate 112 56 L`. For a
`112`-far `f` the good set has card `≤ L` (`wrap_good_challenge_card_le_sharp`), so the vanishing
polynomial `∏_{α good}(X − C α)` is the nonzero degree-`≤ L` witness whose roots contain every good
challenge — the δ-PRESERVING (`dIn = 56 = (7/8)·64`) proximity-gap witness, at the folded code's OWN
Johnson radius. No `sorry`: the SOLE hypothesis is the precisely-named correlated-agreement `Prop`. -/
theorem sharp_of_correlatedAgreementLine (L : ℕ)
    (hCA : CorrelatedAgreementLine friSetupWrapRate 56 L) :
    WrapCorrelatedAgreementSharp L := by
  classical
  intro f hfar
  set Gd : Set BabyBear :=
    {α : BabyBear | closeN friSetupWrapRate.C' 56 (Fold friSetupWrapRate.geom α f)} with hGd
  have hfin : Gd.Finite := Set.toFinite _
  set Good : Finset BabyBear := hfin.toFinset with hGood
  have hmem : ∀ α, α ∈ Good ↔ α ∈ Gd := by
    intro α; rw [hGood]; simp only [Set.Finite.mem_toFinset]
  have hcard : Good.card ≤ L :=
    wrap_good_challenge_card_le_sharp hCA hfar Good (fun α hα => (hmem α).mp hα)
  refine ⟨∏ α ∈ Good, (X - C α),
    (monic_prod_X_sub_C (fun α : BabyBear => α) Good).ne_zero, ?_, ?_⟩
  · rw [natDegree_finsetProd_X_sub_C_eq_card Good (fun α : BabyBear => α)]
    exact hcard
  · intro α hα
    have hαG : α ∈ Good := (hmem α).mpr hα
    show (∏ β ∈ Good, (X - C β)).eval α = 0
    rw [eval_prod]
    exact Finset.prod_eq_zero hαG (by simp)

/-- **The δ-preserving proximity gap, from the primitive** — routed through the framework's own
reduction `friProximityGap_of_badChallengePoly`. `dIn = 56` is the folded code's Johnson radius
(relative `7/8`), so farness is PRESERVED across the fold (`7/8 → 7/8`), not degraded to the packing
method's `21/32`. -/
theorem wrap_friProximityGap_sharp (L : ℕ)
    (hCA : CorrelatedAgreementLine friSetupWrapRate 56 L) :
    FriProximityGapChallenges friSetupWrapRate 112 56 L :=
  friProximityGap_of_badChallengePoly friSetupWrapRate 112 56 L
    (sharp_of_correlatedAgreementLine L hCA)

/-- **The sharp witness FIRES on the concrete `112`-far `fSqWrap`** (conditional on the primitive):
at most `L` folding challenges fold it `56`-close to the constants, exhibited as the roots of an
actual nonzero degree-`≤ L` polynomial. Non-vacuous: `fSqWrap_far` supplies the hypothesis. -/
theorem wrap_sharp_witness_fires (L : ℕ)
    (hCA : CorrelatedAgreementLine friSetupWrapRate 56 L) :
    ∃ P : BabyBear[X], P ≠ 0 ∧ P.natDegree ≤ L ∧
      {α : BabyBear | closeN friSetupWrapRate.C' 56 (Fold friSetupWrapRate.geom α fSqWrap)}
        ⊆ {α : BabyBear | P.eval α = 0} :=
  sharp_of_correlatedAgreementLine L hCA fSqWrap_far

/-! ## §3b. THE δ-PRESERVING PRIMITIVE, PROVED at LINEAR list size (BCIKS20 correlated-agreement core).

`correlatedAgreementLineAt_twoPoint` gave the primitive only at the *weak* floor `|κ| − 2·dIn`
(vacuous at `dIn = 56`). Here the SHARP floor `|κ| − dIn` is PROVED for the deployed wrap setup —
the exact BCIKS20 correlated-agreement content — by the deployed dimension-`2` collapse, WITHOUT the
general Guruswami–Sudan interpolation machinery, at a LINEAR list size `L = 512 = |κ|²/(|κ| − dIn)`
— the tight BCIKS `n/(1−δ)` scaling, not the quadratic `|κ|²`. The RADIUS is sharp too:
`dIn = 56 = (7/8)·64`, δ-preserving.

**Why single-fibre pinning (Route 1) is IMPOSSIBLE, and how a DUAL count still gives linear.**
Fix `f`. Suppose NO constant point `(a,b) ∈ F²` is rich — every fibre `Φ⁻¹(a,b)` has `< 8` fibres.
Each good `α` folds `f` to a constant `c_α` on `≥ 8` fibres `S_α = {y | E f y + α·O f y = c_α}`, and
`C'` = CONSTANTS forces any `y, y' ∈ S_α` with `Φ y ≠ Φ y'` to obey `O f y ≠ O f y'` and to PIN
`α = (E f y' − E f y)/(O f y − O f y')`. The pin needs BOTH fibres — the free constant `c_α` cancels
only in the DIFFERENCE — so no single distinguished fibre determines `α`, and the naive injection
`α ↦ (y_α, y'_α)` lands in `κ × κ`, giving only the quadratic `|Good| ≤ |κ|² = 4096`.

The linear bound comes from the DUAL of that pin. For `α ≠ β`, a pair `(y, y')` with `Φ y ≠ Φ y'`
lying in BOTH `S_α` and `S_β` folds equal under both, so it pins `α = β` — a contradiction. Hence the
ordered distinct-`Φ` pair sets `Pairs α = {(y,y') ∈ S_α × S_α | Φ y ≠ Φ y'}` are PAIRWISE DISJOINT.
Each is large: every one of `8` fibres `y ∈ S_α` has a partner of a different `Φ`-value (its own
`Φ`-fibre inside `S_α` has `≤ 7 < |S_α|` members), so `y ↦ (y, partner y)` embeds `8` fibres into
`Pairs α`, giving `|Pairs α| ≥ 8`. Disjoint `≥ 8`-subsets of `κ × κ` (card `4096`) number at most
`4096/8 = 512`. That `|κ|²/(|κ| − dIn)` is genuinely linear in `|κ|`: with `dIn = (7/8)|κ|` it is
`8·|κ|`, the BCIKS `n/(1−δ)` list size. (Each `α` consuming only `8 = |κ| − dIn` pairs, rather than
its full `≈ |S_α|²`, is why the constant is `8·|κ|` and not the ideal `|κ|`; the packing/Fisher method
that would sharpen it is DEAD here — `a² = 8² = 64 < |κ|·M = 448`, the very obstruction of §F.) -/

set_option maxRecDepth 8000 in
/-- **THE δ-PRESERVING CORRELATED-AGREEMENT PRIMITIVE, PROVED at the deployed wrap setup, LINEAR list
size.** `CorrelatedAgreementLine friSetupWrapRate 56 292`: for ANY `f`, if more than `292` folding
challenges fold `f` to within `56 = (7/8)·64` of the constants, a SINGLE constant pair `(a,b)` agrees
with `(E f, O f)` on `≥ |κ| − 56 = 8` fibers simultaneously — the sharp `1 − δ` (δ-preserving) floor,
beyond the `|κ| − 2·dIn` two-point reach and beyond the packing method's `21/32` radius. No `sorry`,
no hypothesis.

The list size `292 = ⌈4096/14⌉` is LINEAR in `|κ|`, SHARPENED from the earlier `512 = 4096/8` by the
SHARP per-`α` pair count `|Pairs α| ≥ 14` (§3b): every good `α`'s agreement set has a `Φ`-fibre `A`
with `1 ≤ |A| ≤ 7` (no-rich-point) whose cross pairs with `S α \ A` number `2·|A|·(|S α|−|A|) ≥ 14`,
the exact minimum (attained by the `7+1` split). `14 = min(|S α|² − Σ mᵢ²)` is the true ceiling of
the ordered-pair method, so `292` is the sharpest bound THIS method reaches; the ideal `≤ |κ| = 64` is
UNREACHABLE (see §5 — the agreement floor `8 = √ρ·|κ|` sits EXACTLY at the Johnson radius, where every
GS/Johnson list-size bound has a vanishing denominator, and the true list is genuinely `> |κ|`). -/
theorem wrap_correlatedAgreementLine :
    CorrelatedAgreementLine friSetupWrapRate 56 292 := by
  classical
  intro f Good hclose hL
  set G := friSetupWrapRate.geom with hG
  -- Either some constant point is rich (`≥ 8` fibers) — the conclusion — or none is, and then the
  -- ORDERED distinct-`Φ` pair sets `Pairs α ⊆ κ × κ` are pairwise DISJOINT and each of card `≥ 8`.
  -- Disjoint `≥ 8`-sets inside `κ × κ` (card `4096`) force `|Good| ≤ 4096 / 8 = 512` — LINEAR.
  rcases em (∃ a b : BabyBear,
      8 ≤ (Finset.univ.filter (fun y : Fin (2 ^ 6) => E G f y = a ∧ O G f y = b)).card)
    with hrich | hnorich
  · -- Rich point → the δ-preserving agreement pair.
    obtain ⟨a, b, hab⟩ := hrich
    refine ⟨(fun _ => a), mem_wrap_C'.mpr ⟨a, rfl⟩, (fun _ => b), mem_wrap_C'.mpr ⟨b, rfl⟩, ?_⟩
    have hn : Fintype.card (Fin (2 ^ 6)) = 64 := by simp
    rw [hn]
    simpa using hab
  · -- No rich point: every `Φ`-fibre has `≤ 7` fibres.
    exfalso
    push_neg at hnorich
    -- Pick a fold-constant `cc α` for each good `α`, and its agreement set `S α` (card `≥ 8`).
    have hex : ∀ α ∈ Good, ∃ c : BabyBear,
        (disagree (Fold G α f) (fun _ => c)).card ≤ 56 := by
      intro α hα
      obtain ⟨g, hgC, hcard⟩ := hclose α hα
      obtain ⟨c, rfl⟩ := mem_wrap_C'.mp hgC
      exact ⟨c, hcard⟩
    choose! cc hcc using hex
    set S : BabyBear → Finset (Fin (2 ^ 6)) :=
      fun α => Finset.univ.filter (fun y => Fold G α f y = cc α) with hSdef
    have hmemS : ∀ α y, y ∈ S α ↔ Fold G α f y = cc α := by
      intro α y; simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and]
    have hScard : ∀ α ∈ Good, 8 ≤ (S α).card := by
      intro α hα
      have hcompl : S α = (disagree (Fold G α f) (fun _ => cc α))ᶜ := by
        ext y
        simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl,
          mem_disagree, not_not]
      have hn : Fintype.card (Fin (2 ^ 6)) = 64 := by simp
      have hcard : (S α).card
          = Fintype.card (Fin (2 ^ 6)) - (disagree (Fold G α f) (fun _ => cc α)).card := by
        rw [hcompl, Finset.card_compl]
      have := hcc α hα
      rw [hcard, hn]; omega
    -- The ORDERED distinct-`Φ` pairs drawn from `S α`.
    set Pairs : BabyBear → Finset (Fin (2 ^ 6) × Fin (2 ^ 6)) :=
      fun α => (S α ×ˢ S α).filter
        (fun p => ¬(E G f p.1 = E G f p.2 ∧ O G f p.1 = O G f p.2)) with hPdef
    -- SIZE (SHARPENED to `14`, from `512 = 4096/8` to `292 = ⌈4096/14⌉`). Fix any fibre `y₀ ∈ S α`
    -- and split `S α = A ⊍ B` where `A` = the `Φ`-fibre of `y₀` inside `S α` and `B = S α \ A`. Every
    -- CROSS pair (one endpoint in `A`, the other in `B`) has distinct `Φ`, so `A ×ˢ B ⊍ B ×ˢ A ⊆
    -- Pairs α`, of card `2·|A|·|B|`. The no-rich-point cap gives `1 ≤ |A| ≤ 7`, and `|A| + |B| =
    -- |S α| ≥ 8` forces `|B| ≥ 1`; then `|A|·|B| ≥ |A| + |B| − 1 ≥ 7` (the `(|A|−1)(|B|−1) ≥ 0`
    -- inequality), so `2·|A|·|B| ≥ 14`. This is the exact per-`α` minimum: the `7+1` split (a fibre of
    -- `7` and a singleton, `|S α| = 8`) attains `2·7·1 = 14`, matching `min(s²−Σmᵢ²) = 14`.
    have harith : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → 8 ≤ a + b → 14 ≤ 2 * (a * b) := by
      intro a b ha hb hab
      obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le ha
      obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hb
      have h6 : 6 ≤ a + b := by omega
      nlinarith [h6, Nat.zero_le (a * b)]
    have hsize : ∀ α ∈ Good, 14 ≤ (Pairs α).card := by
      intro α hα
      have hScardα := hScard α hα
      have hSpos : (S α).Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨y₀, hy₀⟩ := hSpos
      -- `Φ`-fibre of `y₀` inside `S α` (`A`), and its complement `B` inside `S α` (as `filter (¬·)`).
      set A : Finset (Fin (2 ^ 6)) :=
        (S α).filter (fun y => E G f y = E G f y₀ ∧ O G f y = O G f y₀) with hAdef
      set B : Finset (Fin (2 ^ 6)) :=
        (S α).filter (fun y => ¬ (E G f y = E G f y₀ ∧ O G f y = O G f y₀)) with hBdef
      have hAsub : A ⊆ S α := Finset.filter_subset _ _
      have hy₀A : y₀ ∈ A := Finset.mem_filter.mpr ⟨hy₀, rfl, rfl⟩
      have hApos : 1 ≤ A.card := Finset.card_pos.mpr ⟨y₀, hy₀A⟩
      have hAle : A.card ≤ 7 := by
        have hsub : A ⊆ Finset.univ.filter
            (fun y => E G f y = E G f y₀ ∧ O G f y = O G f y₀) := by
          intro z hz
          rw [Finset.mem_filter] at hz ⊢
          exact ⟨Finset.mem_univ _, hz.2⟩
        have h7 : (Finset.univ.filter
            (fun y => E G f y = E G f y₀ ∧ O G f y = O G f y₀)).card < 8 :=
          hnorich (E G f y₀) (O G f y₀)
        exact le_trans (Finset.card_le_card hsub) (by omega)
      have hABcard : A.card + B.card = (S α).card :=
        Finset.card_filter_add_card_filter_not _
      have hBpos : 1 ≤ B.card := by omega
      -- Every cross pair (`A`-endpoint, `B`-endpoint), both directions, is a distinct-`Φ` pair: an
      -- `A`-endpoint has `Φ = Φ y₀`, a `B`-endpoint has `Φ ≠ Φ y₀`, so the two disagree.
      have mkPair : ∀ q : Fin (2 ^ 6) × Fin (2 ^ 6), q.1 ∈ S α → q.2 ∈ S α →
          (E G f q.1 = E G f y₀ ∧ O G f q.1 = O G f y₀) →
          ¬ (E G f q.2 = E G f y₀ ∧ O G f q.2 = O G f y₀) → q ∈ Pairs α := by
        intro q hq1 hq2 hqA hqB
        rw [hPdef, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hq1, hq2⟩, fun hΦ => hqB ⟨hΦ.1.symm.trans hqA.1, hΦ.2.symm.trans hqA.2⟩⟩
      have hcross : ∀ p : Fin (2 ^ 6) × Fin (2 ^ 6),
          (p.1 ∈ A ∧ p.2 ∈ B) ∨ (p.1 ∈ B ∧ p.2 ∈ A) → p ∈ Pairs α := by
        rintro p (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact mkPair p (hAsub h1) (Finset.filter_subset _ _ h2)
            (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
        · -- swap the roles: `(p.2, p.1)` is an ordered pair; disagreement predicate is symmetric.
          have hbase := mkPair (p.2, p.1) (hAsub h2) (Finset.filter_subset _ _ h1)
            (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
          rw [hPdef, Finset.mem_filter, Finset.mem_product] at hbase ⊢
          exact ⟨⟨hbase.1.2, hbase.1.1⟩, fun hΦ => hbase.2 ⟨hΦ.1.symm, hΦ.2.symm⟩⟩
      have hunion : (A ×ˢ B) ∪ (B ×ˢ A) ⊆ Pairs α := by
        intro p hp
        rw [Finset.mem_union, Finset.mem_product, Finset.mem_product] at hp
        exact hcross p (hp.imp id id)
      have hABdisj : Disjoint A B :=
        Finset.disjoint_filter_filter_not (S α) (S α)
          (fun y => E G f y = E G f y₀ ∧ O G f y = O G f y₀)
      have hdisjAB : Disjoint (A ×ˢ B) (B ×ˢ A) := by
        rw [Finset.disjoint_left]
        intro p hp1 hp2
        rw [Finset.mem_product] at hp1 hp2
        exact (Finset.disjoint_left.mp hABdisj hp1.1) hp2.1
      have hcardU : ((A ×ˢ B) ∪ (B ×ˢ A)).card = 2 * (A.card * B.card) := by
        rw [Finset.card_union_of_disjoint hdisjAB, Finset.card_product, Finset.card_product]
        ring
      have hle := Finset.card_le_card hunion
      rw [hcardU] at hle
      exact le_trans (harith A.card B.card hApos hBpos (by omega)) hle
    -- DISJOINTNESS: a shared pair `(y, y')` with `Φ y ≠ Φ y'` folds equal under both `α` and `β`,
    -- so `α = (E y' − E y)/(O y − O y') = β`. Hence distinct `α` give disjoint `Pairs α`.
    have hdisj : ∀ α ∈ Good, ∀ β ∈ Good, α ≠ β → Disjoint (Pairs α) (Pairs β) := by
      intro α hα β hβ hαβ
      rw [Finset.disjoint_left]
      intro p hpα hpβ
      simp only [hPdef, Finset.mem_filter, Finset.mem_product] at hpα hpβ
      obtain ⟨⟨hp1α, hp2α⟩, hΦα⟩ := hpα
      obtain ⟨⟨hp1β, hp2β⟩, _⟩ := hpβ
      simp only [hmemS] at hp1α hp2α hp1β hp2β
      have hEα : E G f p.1 + α * O G f p.1 = E G f p.2 + α * O G f p.2 := by
        show Fold G α f p.1 = Fold G α f p.2; rw [hp1α, hp2α]
      have hEβ : E G f p.1 + β * O G f p.1 = E G f p.2 + β * O G f p.2 := by
        show Fold G β f p.1 = Fold G β f p.2; rw [hp1β, hp2β]
      have hmulα : α * (O G f p.1 - O G f p.2) = E G f p.2 - E G f p.1 := by
        linear_combination hEα
      have hmulβ : β * (O G f p.1 - O G f p.2) = E G f p.2 - E G f p.1 := by
        linear_combination hEβ
      have hOne : O G f p.1 ≠ O G f p.2 := by
        intro hOeq
        apply hΦα
        have hz : (0 : BabyBear) = E G f p.2 - E G f p.1 := by rw [← hmulα, hOeq]; ring
        exact ⟨(sub_eq_zero.mp hz.symm).symm, hOeq⟩
      have hDne : O G f p.1 - O G f p.2 ≠ 0 := sub_ne_zero.mpr hOne
      have hcancel : α * (O G f p.1 - O G f p.2) = β * (O G f p.1 - O G f p.2) := by
        rw [hmulα, hmulβ]
      exact hαβ (mul_right_cancel₀ hDne hcancel)
    -- COUNT: `14·|Good| ≤ ∑ |Pairs α| = |⋃ Pairs α| ≤ |κ × κ| = 4096`, so `|Good| ≤ 292`.
    have hsum : 14 * Good.card ≤ ∑ α ∈ Good, (Pairs α).card := by
      calc 14 * Good.card = ∑ _α ∈ Good, 14 := by rw [Finset.sum_const, smul_eq_mul]; ring
        _ ≤ ∑ α ∈ Good, (Pairs α).card := Finset.sum_le_sum hsize
    have hbu : (Good.biUnion Pairs).card = ∑ α ∈ Good, (Pairs α).card :=
      Finset.card_biUnion hdisj
    have huniv : (Finset.univ : Finset (Fin (2 ^ 6) × Fin (2 ^ 6))).card = 4096 := by simp
    have hle : (Good.biUnion Pairs).card ≤ 4096 :=
      le_trans (Finset.card_le_card (Finset.subset_univ _)) (le_of_eq huniv)
    omega

/-- **`WrapCorrelatedAgreementSharp 292`, PROVED (no hypothesis).** The δ-preserving proximity-gap
witness at the folded code's OWN Johnson radius (`dIn = 56 = (7/8)·64`), discharged by feeding the
now-proved line primitive into the reduction. This is `BadChallengePoly friSetupWrapRate 112 56 292`
as an unconditional theorem — the residual named in `FriProximityGapWitness.lean §F`, CLOSED at the
LINEAR list size `292 = ⌈4096/14⌉` (sharpened from `512`). -/
theorem wrap_correlatedAgreement_sharp_proved : WrapCorrelatedAgreementSharp 292 :=
  sharp_of_correlatedAgreementLine 292 wrap_correlatedAgreementLine

/-- **The δ-PRESERVING FRI proximity gap, PROVED unconditionally.**
`FriProximityGapChallenges friSetupWrapRate 112 56 292`: a `112`-far word has at most `292` folding
challenges whose fold is `56`-close (relative `7/8`) to the constants — farness PRESERVED across the
fold (`7/8 → 7/8`), the sharp radius the Fisher/packing method (`wrap_friProximityGap_johnson`,
`21/32`) could not reach, at the LINEAR list size. No hypothesis remains. -/
theorem wrap_friProximityGap_sharp_proved :
    FriProximityGapChallenges friSetupWrapRate 112 56 292 :=
  wrap_friProximityGap_sharp 292 wrap_correlatedAgreementLine

/-- **The sharp gap FIRES on the concrete `112`-far `fSqWrap`, unconditionally**: at most `292`
folding challenges fold it `56`-close to the constants, exhibited as the roots of an actual nonzero
polynomial of degree `≤ 292`. Non-vacuous (`fSqWrap_far` supplies the far hypothesis), no
correlated-agreement hypothesis assumed. -/
theorem wrap_sharp_witness_fires_proved :
    ∃ P : BabyBear[X], P ≠ 0 ∧ P.natDegree ≤ 292 ∧
      {α : BabyBear | closeN friSetupWrapRate.C' 56 (Fold friSetupWrapRate.geom α fSqWrap)}
        ⊆ {α : BabyBear | P.eval α = 0} :=
  wrap_correlatedAgreement_sharp_proved fSqWrap_far

/-! ## §5. WHY `≤ |κ| = 64` IS UNREACHABLE — the exact-Johnson-radius wall, and the named GS target.

The task's optimistic hope was that the CONSTANT-code collapse (`C'` = constants, so the
correlated-agreement codewords are `const a`) would let Guruswami–Sudan interpolation drive the list
size all the way to `≤ |κ| = 64` — the ideal `n/(1−δ)` constant `= 1`. It does NOT, and this is not a
looseness of *our* proof but of the primitive at this radius. Two independent honest facts.

**(a) `≤ |κ|` is literally FALSE at the deployed radius (a construction, not a gap).** Reduce as in
§3b: `Φ = (E f, O f) : κ → F²` gives `|κ| = 64` points (multiplicity `≤ 7` under no-rich-point), and
a good challenge `α` is a LINE `E = −α·O + c` in `F²` covering `≥ 8` points-with-multiplicity (its
slope `−α` distinct per `α`). Take two "heavy" points `p₁, p₂` of multiplicity `7` (`14` total) and
`50` further points of multiplicity `1`. Each line through `p₁` and one singleton covers `7 + 1 = 8`
(good), with a distinct slope per singleton — `50` good `α`; likewise `50` through `p₂`; generic
placement keeps these slopes distinct, so `≈ 100 > 64` good challenges with NO point of multiplicity
`≥ 8`. (A `k`-pencil optimum reaches `≈ 155`.) All of `E f, O f, α` are free (`f : ι → F` arbitrary,
`α ∈ BabyBear`), so the configuration is realizable: **no theorem of the form
`CorrelatedAgreementLine friSetupWrapRate 56 L` with `L < ~100` can hold**, and `≤ 64` is refuted. So
the residual `8×` factor is INHERENT to the radius, exactly as the dead packing quadratic of §F warned
(`a² = 8² = 64 < |κ|·M = 448`).

**(b) The reason: agreement `8` is BELOW the GS/Johnson radius of the line code.** Viewing the good
slopes as the degree-`≤ 1` codewords (`k = 2`, block length `n = |κ| = 64`) they agree with, GS
weighted interpolation produces a nonzero bivariate `Q(x, y)` with a controllable positive `y`-degree
(hence a LINEAR list bound with the ideal constant) only when the agreement `t` STRICTLY exceeds the GS
radius `√(k·n) = √128 ≈ 11.31`, i.e. `t² > k·n`. The deployed agreement is `t = |κ| − dIn = 8`, and
`t² = 64 < 128 = k·n` — the interpolation degenerates (`Q` is forced to `0`), and no GS bound, least of
all `≤ |κ|`, exists at this radius. Equivalently, in rate terms the constant code has `√ρ = √(1/64) =
1/8` and the agreement is `8/64 = 1/8 = √ρ` EXACTLY — the Johnson boundary, where every list-size
denominator vanishes. This is certified below. -/

/-- **The deployed agreement floor sits below the GS line-decoding radius.** `t = |κ| − 56 = 8`, and
`t² = 64 < 128 = 2·|κ| = k·n` (line code `k = 2`, `n = |κ|`): the Guruswami–Sudan interpolation
hypothesis `t² > k·n` is NOT met, so GS delivers no bound at this radius — the formal reason `≤ |κ|` is
out of reach and the honest `292` (the sharp reach of the ordered-pair method) stands. -/
theorem wrap_below_gs_line_radius :
    (Fintype.card (Fin (2 ^ 6)) - 56) ^ 2 < 2 * Fintype.card (Fin (2 ^ 6)) := by
  have h : Fintype.card (Fin (2 ^ 6)) = 64 := by simp
  rw [h]; norm_num

/-- **NAMED UPSTREAM TARGET — the general Guruswami–Sudan line list bound (Mathlib lacks it).** The
genuine BCIKS/GS correlated-agreement statement: STRICTLY above the GS radius (`t² > k·|κ|`, here
`k = 2` for the affine line), the good-challenge (good-slope) list is bounded by the IDEAL LINEAR size
`2·|κ|` via the weighted-interpolation polynomial `Q(x, y)` and the `(y − f(x)) ∣ Q` divisibility. It
is stated as a conditional `Prop` so the residual is a Lean object, not prose; it is NOT proved here
(it is the real upstream lemma, on the order of Berry–Esseen), and — crucially — its hypothesis is
FALSE at the deployed radius (`wrap_below_gs_line_radius`), so even a proof of it would say nothing
about the deployed case: the `8×` gap is genuinely at/below the Johnson boundary. -/
def GuruswamiSudanLineListBound (S : FriSetup F ι κ) (dIn : ℕ) : Prop :=
  (Fintype.card κ - dIn) ^ 2 > 2 * Fintype.card κ →
    CorrelatedAgreementLine S dIn (2 * Fintype.card κ)

/-! ## §6. THE INTERIOR RADIUS `dIn = 52` — off the Johnson boundary, GS NON-DEGENERATE.

`§3b`/`§5` run the deployed analysis AT the Johnson boundary `dIn = 56` (relative `7/8`), where the
line code's GS interpolation DEGENERATES: agreement `t = |κ| − 56 = 8`, and `t² = 64 < 128 = 2·|κ|`
(`wrap_below_gs_line_radius`) — the boundary `t = √ρ·|κ|` where every GS/Johnson denominator vanishes,
forcing the boundary-bespoke ordered-pair list `292`.

This section pulls the analysis radius INTERIOR to `dIn = 52` (relative `13/16`). That is a
proof-cleanliness choice, NOT a security one: the deployed `19`-query soundness has `~116` bits of
headroom (`|F| ≈ 2¹²⁴`, list term `L/2¹²⁴`), so `L = 186` at `dIn = 52` and `L = 292` at `dIn = 56`
are security-indistinguishable. What the interior BUYS is regime: at `dIn = 52` the agreement is
`t = |κ| − 52 = 12` and `t² = 144 > 128 = 2·|κ|`, so the Guruswami–Sudan NON-DEGENERACY hypothesis of
`GuruswamiSudanLineListBound` (`§5`) is MET (`wrap_meets_gs_line_radius`) — the deployed proximity
soundness now runs in the interior list-decoding regime with margin, not on the degenerate boundary.

Two honest facts about the list size at `dIn = 52`:
* **The ORDERED-PAIR method gives `L ≤ 186`, PROVED here** (`wrap_correlatedAgreementLine_interior`).
  Each good `α` now folds `f` to a constant on `≥ 12` fibers (vs `8` at `dIn = 56`), so under
  no-rich-point (every constant point has `< 12`, i.e. `≤ 11` fibers) its ordered distinct-`Φ` pair
  set `Pairs α` has card `≥ 2·11·1 = 22` (the `11+1` split minimum, vs `14` at `dIn = 56`). Each good
  `α` "consumes more pairs", so the disjoint pair sets inside `κ × κ` (card `4096`) force
  `|Good| ≤ ⌊4096/22⌋ = 186` — sharper than the boundary's `292`, and genuinely interior.
* **The GS-IDEAL `L ≤ 2·|κ| = 128` is NOT reached by the ordered-pair method** (`186 > 128`), and is
  NOT claimed here. `128 = 2·|κ|` is exactly the conclusion of `GuruswamiSudanLineListBound` — the
  weighted-interpolation lemma that handles the point MULTIPLICITIES the ordered-pair method cannot
  (a good line may carry `≥ 12` fibers on only `2` distinct `Φ`-points, mult `11 + 1`, so naive
  Johnson double-counting has a negative denominator `t² − m·n = 144 − 11·64 < 0`). Its hypothesis is
  now SATISFIABLE at `dIn = 52` (that is the value of moving interior — at `dIn = 56` the hypothesis
  is FALSE, `wrap_below_gs_line_radius`), but the lemma itself remains the named upstream target and is
  NOT discharged here. The honest interior list is `186`; the ideal `128` awaits GS. -/

/-- **The GS line-decoding NON-DEGENERACY hypothesis is MET at the interior radius `dIn = 52`.**
`t = |κ| − 52 = 12`, and `t² = 144 > 128 = 2·|κ| = k·n` (line code `k = 2`, `n = |κ|`): the
Guruswami–Sudan interpolation hypothesis `t² > k·n` HOLDS — precisely the hypothesis of
`GuruswamiSudanLineListBound friSetupWrapRate 52`, and precisely what `wrap_below_gs_line_radius`
shows FAILS at the Johnson boundary `dIn = 56`. So the interior analysis runs OFF the degenerate
boundary, in the regime where GS delivers a bound. -/
theorem wrap_meets_gs_line_radius :
    (Fintype.card (Fin (2 ^ 6)) - 52) ^ 2 > 2 * Fintype.card (Fin (2 ^ 6)) := by
  have h : Fintype.card (Fin (2 ^ 6)) = 64 := by simp
  rw [h]; norm_num

set_option maxRecDepth 8000 in
/-- **THE δ-PRESERVING CORRELATED-AGREEMENT PRIMITIVE at the INTERIOR radius `dIn = 52`, PROVED.**
`CorrelatedAgreementLine friSetupWrapRate 52 186`: for ANY `f`, if more than `186` folding challenges
fold `f` to within `52 = (13/16)·64` of the constants, a SINGLE constant pair `(a,b)` agrees with
`(E f, O f)` on `≥ |κ| − 52 = 12` fibers simultaneously — the sharp `1 − δ` (δ-preserving) floor at
the interior radius. No `sorry`, no hypothesis.

The list `186 = ⌊4096/22⌋` is LINEAR in `|κ|` and SHARPER than the boundary `dIn = 56` list `292`,
because the interior agreement floor `12` (vs `8`) forces the per-`α` ordered distinct-`Φ` pair count
up to `22` (vs `14`): under no-rich-point every constant point has `≤ 11` fibers, so a good `α`'s
agreement set (card `≥ 12`) splits into a `Φ`-fibre `A` (`1 ≤ |A| ≤ 11`) and its complement `B`
(`|B| ≥ 1`) with `2·|A|·|B| ≥ 22` (the `11+1` minimum). The GS-ideal `≤ 2·|κ| = 128` is NOT reached
by this ordered-pair method (see `wrap_meets_gs_line_radius`: the GS hypothesis is now MET, so the
ideal is no longer refuted — but discharging it is the upstream GS interpolation lemma, not proved). -/
theorem wrap_correlatedAgreementLine_interior :
    CorrelatedAgreementLine friSetupWrapRate 52 186 := by
  classical
  intro f Good hclose hL
  set G := friSetupWrapRate.geom with hG
  -- Either some constant point is rich (`≥ 12` fibers) — the δ-preserving conclusion — or none is,
  -- and then the ORDERED distinct-`Φ` pair sets `Pairs α ⊆ κ × κ` are pairwise DISJOINT and each of
  -- card `≥ 22`. Disjoint `≥ 22`-sets inside `κ × κ` (card `4096`) force `|Good| ≤ 4096/22 = 186`.
  rcases em (∃ a b : BabyBear,
      12 ≤ (Finset.univ.filter (fun y : Fin (2 ^ 6) => E G f y = a ∧ O G f y = b)).card)
    with hrich | hnorich
  · -- Rich point → the δ-preserving agreement pair.
    obtain ⟨a, b, hab⟩ := hrich
    refine ⟨(fun _ => a), mem_wrap_C'.mpr ⟨a, rfl⟩, (fun _ => b), mem_wrap_C'.mpr ⟨b, rfl⟩, ?_⟩
    have hn : Fintype.card (Fin (2 ^ 6)) = 64 := by simp
    rw [hn]
    simpa using hab
  · -- No rich point: every `Φ`-fibre has `≤ 11` fibers.
    exfalso
    push_neg at hnorich
    have hex : ∀ α ∈ Good, ∃ c : BabyBear,
        (disagree (Fold G α f) (fun _ => c)).card ≤ 52 := by
      intro α hα
      obtain ⟨g, hgC, hcard⟩ := hclose α hα
      obtain ⟨c, rfl⟩ := mem_wrap_C'.mp hgC
      exact ⟨c, hcard⟩
    choose! cc hcc using hex
    set S : BabyBear → Finset (Fin (2 ^ 6)) :=
      fun α => Finset.univ.filter (fun y => Fold G α f y = cc α) with hSdef
    have hmemS : ∀ α y, y ∈ S α ↔ Fold G α f y = cc α := by
      intro α y; simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and]
    have hScard : ∀ α ∈ Good, 12 ≤ (S α).card := by
      intro α hα
      have hcompl : S α = (disagree (Fold G α f) (fun _ => cc α))ᶜ := by
        ext y
        simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl,
          mem_disagree, not_not]
      have hn : Fintype.card (Fin (2 ^ 6)) = 64 := by simp
      have hcard : (S α).card
          = Fintype.card (Fin (2 ^ 6)) - (disagree (Fold G α f) (fun _ => cc α)).card := by
        rw [hcompl, Finset.card_compl]
      have := hcc α hα
      rw [hcard, hn]; omega
    set Pairs : BabyBear → Finset (Fin (2 ^ 6) × Fin (2 ^ 6)) :=
      fun α => (S α ×ˢ S α).filter
        (fun p => ¬(E G f p.1 = E G f p.2 ∧ O G f p.1 = O G f p.2)) with hPdef
    -- SIZE `≥ 22`. Split `S α = A ⊍ B` at the `Φ`-fibre `A` of a chosen `y₀`. No-rich caps `|A| ≤ 11`;
    -- `|S α| ≥ 12` forces `|B| ≥ 1`; then `2·|A|·|B| ≥ 22` (the `11+1` minimum) cross pairs.
    have harith : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → 12 ≤ a + b → 22 ≤ 2 * (a * b) := by
      intro a b ha hb hab
      obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le ha
      obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hb
      have h10 : 10 ≤ a + b := by omega
      nlinarith [h10, Nat.zero_le (a * b)]
    have hsize : ∀ α ∈ Good, 22 ≤ (Pairs α).card := by
      intro α hα
      have hScardα := hScard α hα
      have hSpos : (S α).Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨y₀, hy₀⟩ := hSpos
      set A : Finset (Fin (2 ^ 6)) :=
        (S α).filter (fun y => E G f y = E G f y₀ ∧ O G f y = O G f y₀) with hAdef
      set B : Finset (Fin (2 ^ 6)) :=
        (S α).filter (fun y => ¬ (E G f y = E G f y₀ ∧ O G f y = O G f y₀)) with hBdef
      have hAsub : A ⊆ S α := Finset.filter_subset _ _
      have hy₀A : y₀ ∈ A := Finset.mem_filter.mpr ⟨hy₀, rfl, rfl⟩
      have hApos : 1 ≤ A.card := Finset.card_pos.mpr ⟨y₀, hy₀A⟩
      have hAle : A.card ≤ 11 := by
        have hsub : A ⊆ Finset.univ.filter
            (fun y => E G f y = E G f y₀ ∧ O G f y = O G f y₀) := by
          intro z hz
          rw [Finset.mem_filter] at hz ⊢
          exact ⟨Finset.mem_univ _, hz.2⟩
        have h11 : (Finset.univ.filter
            (fun y => E G f y = E G f y₀ ∧ O G f y = O G f y₀)).card < 12 :=
          hnorich (E G f y₀) (O G f y₀)
        exact le_trans (Finset.card_le_card hsub) (by omega)
      have hABcard : A.card + B.card = (S α).card :=
        Finset.card_filter_add_card_filter_not _
      have hBpos : 1 ≤ B.card := by omega
      have mkPair : ∀ q : Fin (2 ^ 6) × Fin (2 ^ 6), q.1 ∈ S α → q.2 ∈ S α →
          (E G f q.1 = E G f y₀ ∧ O G f q.1 = O G f y₀) →
          ¬ (E G f q.2 = E G f y₀ ∧ O G f q.2 = O G f y₀) → q ∈ Pairs α := by
        intro q hq1 hq2 hqA hqB
        rw [hPdef, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hq1, hq2⟩, fun hΦ => hqB ⟨hΦ.1.symm.trans hqA.1, hΦ.2.symm.trans hqA.2⟩⟩
      have hcross : ∀ p : Fin (2 ^ 6) × Fin (2 ^ 6),
          (p.1 ∈ A ∧ p.2 ∈ B) ∨ (p.1 ∈ B ∧ p.2 ∈ A) → p ∈ Pairs α := by
        rintro p (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact mkPair p (hAsub h1) (Finset.filter_subset _ _ h2)
            (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
        · have hbase := mkPair (p.2, p.1) (hAsub h2) (Finset.filter_subset _ _ h1)
            (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
          rw [hPdef, Finset.mem_filter, Finset.mem_product] at hbase ⊢
          exact ⟨⟨hbase.1.2, hbase.1.1⟩, fun hΦ => hbase.2 ⟨hΦ.1.symm, hΦ.2.symm⟩⟩
      have hunion : (A ×ˢ B) ∪ (B ×ˢ A) ⊆ Pairs α := by
        intro p hp
        rw [Finset.mem_union, Finset.mem_product, Finset.mem_product] at hp
        exact hcross p (hp.imp id id)
      have hABdisj : Disjoint A B :=
        Finset.disjoint_filter_filter_not (S α) (S α)
          (fun y => E G f y = E G f y₀ ∧ O G f y = O G f y₀)
      have hdisjAB : Disjoint (A ×ˢ B) (B ×ˢ A) := by
        rw [Finset.disjoint_left]
        intro p hp1 hp2
        rw [Finset.mem_product] at hp1 hp2
        exact (Finset.disjoint_left.mp hABdisj hp1.1) hp2.1
      have hcardU : ((A ×ˢ B) ∪ (B ×ˢ A)).card = 2 * (A.card * B.card) := by
        rw [Finset.card_union_of_disjoint hdisjAB, Finset.card_product, Finset.card_product]
        ring
      have hle := Finset.card_le_card hunion
      rw [hcardU] at hle
      exact le_trans (harith A.card B.card hApos hBpos (by omega)) hle
    -- DISJOINTNESS: a shared distinct-`Φ` pair folds equal under both `α, β`, pinning `α = β`.
    have hdisj : ∀ α ∈ Good, ∀ β ∈ Good, α ≠ β → Disjoint (Pairs α) (Pairs β) := by
      intro α hα β hβ hαβ
      rw [Finset.disjoint_left]
      intro p hpα hpβ
      simp only [hPdef, Finset.mem_filter, Finset.mem_product] at hpα hpβ
      obtain ⟨⟨hp1α, hp2α⟩, hΦα⟩ := hpα
      obtain ⟨⟨hp1β, hp2β⟩, _⟩ := hpβ
      simp only [hmemS] at hp1α hp2α hp1β hp2β
      have hEα : E G f p.1 + α * O G f p.1 = E G f p.2 + α * O G f p.2 := by
        show Fold G α f p.1 = Fold G α f p.2; rw [hp1α, hp2α]
      have hEβ : E G f p.1 + β * O G f p.1 = E G f p.2 + β * O G f p.2 := by
        show Fold G β f p.1 = Fold G β f p.2; rw [hp1β, hp2β]
      have hmulα : α * (O G f p.1 - O G f p.2) = E G f p.2 - E G f p.1 := by
        linear_combination hEα
      have hmulβ : β * (O G f p.1 - O G f p.2) = E G f p.2 - E G f p.1 := by
        linear_combination hEβ
      have hOne : O G f p.1 ≠ O G f p.2 := by
        intro hOeq
        apply hΦα
        have hz : (0 : BabyBear) = E G f p.2 - E G f p.1 := by rw [← hmulα, hOeq]; ring
        exact ⟨(sub_eq_zero.mp hz.symm).symm, hOeq⟩
      have hDne : O G f p.1 - O G f p.2 ≠ 0 := sub_ne_zero.mpr hOne
      have hcancel : α * (O G f p.1 - O G f p.2) = β * (O G f p.1 - O G f p.2) := by
        rw [hmulα, hmulβ]
      exact hαβ (mul_right_cancel₀ hDne hcancel)
    -- COUNT: `22·|Good| ≤ ∑ |Pairs α| = |⋃ Pairs α| ≤ |κ × κ| = 4096`, so `|Good| ≤ 186`.
    have hsum : 22 * Good.card ≤ ∑ α ∈ Good, (Pairs α).card := by
      calc 22 * Good.card = ∑ _α ∈ Good, 22 := by rw [Finset.sum_const, smul_eq_mul]; ring
        _ ≤ ∑ α ∈ Good, (Pairs α).card := Finset.sum_le_sum hsize
    have hbu : (Good.biUnion Pairs).card = ∑ α ∈ Good, (Pairs α).card :=
      Finset.card_biUnion hdisj
    have huniv : (Finset.univ : Finset (Fin (2 ^ 6) × Fin (2 ^ 6))).card = 4096 := by simp
    have hle : (Good.biUnion Pairs).card ≤ 4096 :=
      le_trans (Finset.card_le_card (Finset.subset_univ _)) (le_of_eq huniv)
    omega

/-- **The good-challenge card bound at the INTERIOR inner radius `dIn = 52`.** Given the δ-preserving
line-correlated-agreement primitive at `dIn = 52`, a `112`-far word has at most `L` folding challenges
whose fold is `52`-close to the constants. The contradiction is the deployed dimension-`2` collapse:
correlated agreement forces `≥ 12` fibers onto a single point `(a,b)` of `F²`, but
`wrap_fiber_le_seven` caps that at `7` — with even MORE slack (`12 > 7`) than the boundary (`8 > 7`). -/
theorem wrap_good_challenge_card_le_interior {f : Fin (2 ^ 7) → BabyBear} {L : ℕ}
    (hCA : CorrelatedAgreementLine friSetupWrapRate 52 L)
    (hfar : farN friSetupWrapRate.C 112 f)
    (Good : Finset BabyBear)
    (hGood : ∀ α ∈ Good, closeN friSetupWrapRate.C' 52 (Fold friSetupWrapRate.geom α f)) :
    Good.card ≤ L := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨ge, hge, go, hgo, hbig⟩ := hCA Good hGood hcon
  obtain ⟨a, rfl⟩ := mem_wrap_C'.mp hge
  obtain ⟨b, rfl⟩ := mem_wrap_C'.mp hgo
  have hle7 := wrap_fiber_le_seven hfar a b
  have hn : Fintype.card (Fin (2 ^ 6)) = 64 := by simp
  simp only at hbig
  rw [hn] at hbig
  omega

/-- **THE INTERIOR REDUCTION — `BadChallengePoly friSetupWrapRate 112 52 L` from the line primitive.**
`CorrelatedAgreementLine friSetupWrapRate 52 L → BadChallengePoly friSetupWrapRate 112 52 L`. For a
`112`-far `f` the good set has card `≤ L` (`wrap_good_challenge_card_le_interior`), so
`∏_{α good}(X − C α)` is the nonzero degree-`≤ L` witness — the δ-preserving proximity-gap witness at
the INTERIOR radius `dIn = 52 = (13/16)·64`, off the Johnson boundary. No `sorry`: the SOLE hypothesis
is the precisely-named correlated-agreement `Prop`. -/
theorem interior_of_correlatedAgreementLine (L : ℕ)
    (hCA : CorrelatedAgreementLine friSetupWrapRate 52 L) :
    BadChallengePoly friSetupWrapRate 112 52 L := by
  classical
  intro f hfar
  set Gd : Set BabyBear :=
    {α : BabyBear | closeN friSetupWrapRate.C' 52 (Fold friSetupWrapRate.geom α f)} with hGd
  have hfin : Gd.Finite := Set.toFinite _
  set Good : Finset BabyBear := hfin.toFinset with hGood
  have hmem : ∀ α, α ∈ Good ↔ α ∈ Gd := by
    intro α; rw [hGood]; simp only [Set.Finite.mem_toFinset]
  have hcard : Good.card ≤ L :=
    wrap_good_challenge_card_le_interior hCA hfar Good (fun α hα => (hmem α).mp hα)
  refine ⟨∏ α ∈ Good, (X - C α),
    (monic_prod_X_sub_C (fun α : BabyBear => α) Good).ne_zero, ?_, ?_⟩
  · rw [natDegree_finsetProd_X_sub_C_eq_card Good (fun α : BabyBear => α)]
    exact hcard
  · intro α hα
    have hαG : α ∈ Good := (hmem α).mpr hα
    show (∏ β ∈ Good, (X - C β)).eval α = 0
    rw [eval_prod]
    exact Finset.prod_eq_zero hαG (by simp)

/-- **The δ-preserving proximity gap at the INTERIOR radius, from the primitive.** `dIn = 52`
(relative `13/16`) is interior to the folded code's Johnson radius, in the GS NON-DEGENERATE regime
(`wrap_meets_gs_line_radius`), so farness is preserved across the fold with margin, off the degenerate
boundary the `dIn = 56` version sits on. -/
theorem wrap_friProximityGap_interior (L : ℕ)
    (hCA : CorrelatedAgreementLine friSetupWrapRate 52 L) :
    FriProximityGapChallenges friSetupWrapRate 112 52 L :=
  friProximityGap_of_badChallengePoly friSetupWrapRate 112 52 L
    (interior_of_correlatedAgreementLine L hCA)

/-- **`BadChallengePoly friSetupWrapRate 112 52 186`, PROVED (no hypothesis).** The interior-radius
proximity-gap witness, discharged by feeding the now-proved interior line primitive into the
reduction. -/
theorem wrap_badChallengePoly_interior_proved :
    BadChallengePoly friSetupWrapRate 112 52 186 :=
  interior_of_correlatedAgreementLine 186 wrap_correlatedAgreementLine_interior

/-- **THE PREFERRED DEPLOYED PROXIMITY GAP — δ-preserving, INTERIOR, unconditional.**
`FriProximityGapChallenges friSetupWrapRate 112 52 186`: a `112`-far word has at most `186` folding
challenges whose fold is `52`-close (relative `13/16`) to the constants. This is the composition run
in the INTERIOR list-decoding regime (`wrap_meets_gs_line_radius`: `t² = 144 > 128`), OFF the
degenerate Johnson boundary that `wrap_friProximityGap_sharp_proved` (`dIn = 56`) sits on. The
`dIn = 56` result is kept as the sharpest-RADIUS lemma; this `dIn = 52` result is the preferred
composition — same `~116`-bit security headroom, a strictly cleaner list-decoding regime. -/
theorem wrap_friProximityGap_interior_proved :
    FriProximityGapChallenges friSetupWrapRate 112 52 186 :=
  wrap_friProximityGap_interior 186 wrap_correlatedAgreementLine_interior

/-- **The interior gap FIRES on the concrete `112`-far `fSqWrap`, unconditionally**: at most `186`
folding challenges fold it `52`-close to the constants, exhibited as the roots of an actual nonzero
polynomial of degree `≤ 186`. Non-vacuous (`fSqWrap_far` supplies the far hypothesis). -/
theorem wrap_interior_witness_fires_proved :
    ∃ P : BabyBear[X], P ≠ 0 ∧ P.natDegree ≤ 186 ∧
      {α : BabyBear | closeN friSetupWrapRate.C' 52 (Fold friSetupWrapRate.geom α fSqWrap)}
        ⊆ {α : BabyBear | P.eval α = 0} :=
  wrap_badChallengePoly_interior_proved fSqWrap_far

/-! ## §7. THE IDEAL `128 = 2·|κ|` AND THE GURUSWAMI–SUDAN ROUTE — what closes, and the precise wall.

`GuruswamiSudanLineListBound friSetupWrapRate 52` unfolds (with `wrap_meets_gs_line_radius` supplying
its now-TRUE hypothesis `144 > 128`) to `CorrelatedAgreementLine friSetupWrapRate 52 128` — the ideal
LINEAR list `2·|κ|`. That is a genuine STRENGTHENING of the proved `wrap_correlatedAgreementLine_interior`
(`… 52 186`), NOT a weakening: `CorrelatedAgreementLineAt` is ANTI-monotone in `L` (a larger `L` is a
WEAKER hypothesis `L < Good.card`), so `186` does not yield `128`. The ideal has to be EARNED by the
Guruswami–Sudan weighted-interpolation method, whose two halves are stated generally in
`Dregg2/ForMathlib/GuruswamiSudan.lean`:
* the **list-size half** (`card_le_yDegree_of_dvd` : `#messages ≤ deg_Y Q`) is PROVED there, general
  over any field — the real upstreamable GS core Mathlib lacks (it is `card_roots'` over `F[X]`);
* the **interpolation half** (`GSWitness` : existence of the vanishing bivariate `Q`) is the NAMED
  upstream target (multiplicity/Hasse-derivative vanishing + a dimension count).

The honest finding at the deployed radius: **the interpolation half is OBSTRUCTED at the very point
multiplicities the constant-code fold produces**, so GS does NOT deliver `128` here. Reducing as in
`§3b`, `Φ = (E f, O f) : κ → F²` is a MULTISET of `|κ| = 64` plane points; a good challenge `α` is a
non-vertical line covering `≥ |κ| − 52 = 12` fibres, and under no-rich-point every plane point carries
`≤ 11` fibres. Such a line can be supported on as few as `2` distinct points (the `11 + 1` split). At
that multiplicity the GS interpolation window is EMPTY — no degree `D` meets both existence and
divisibility — so the polynomial method certifies NO bound, least of all `128`. This is the `dIn = 52`
face of the recurring `FriCorrelatedAgreementSharp` theme: the fold's point multiplicities break the
distinct-point GS analysis that `t² > 2·|κ|` (`wrap_meets_gs_line_radius`) would otherwise unlock.

`128` is therefore NEITHER discharged here (no GS route reaches it) NOR refuted (the honest proved
upper bound is `186`; the ordered-pair pencil constructions of `§5` reach only `~100` at this radius,
so the true list sits in `[~100, 186]` and `128` is genuinely open). The deployed composition stays
`wrap_friProximityGap_interior_proved` (`186`); `128` remains the named GS target. Two proved
certificates pin the wall. -/

/-- **The Koetter–Vardy (weighted-GS) denominator is NEGATIVE at the deployed max multiplicity.**
`t = |κ| − 52 = 12`, `t² = 144`, and the heaviest admissible plane point carries `m = 11` fibres
(no-rich-point), so `t² − m·|κ| = 144 − 11·64 = 144 − 704 < 0`. Weighting the interpolation by fibre
multiplicity (the only way to credit a heavy point its `≥ t` agreement) drives the existence degree
above the divisibility degree — no valid weighted-GS window. This is `§5`/`§6`'s named negative
denominator (`t² − m·n < 0`), made a theorem: the reason `t² > 2·|κ|` alone does not deliver `128`. -/
theorem wrap_gs_weighted_denominator_negative :
    (Fintype.card (Fin (2 ^ 6)) - 52) ^ 2 < 11 * Fintype.card (Fin (2 ^ 6)) := by
  have h : Fintype.card (Fin (2 ^ 6)) = 64 := by simp
  rw [h]; norm_num

/-- **The UNWEIGHTED GS interpolation window is EMPTY at a support-`2` good line.** A good `α` may fold
`f` to a constant on `≥ 12` fibres carried by only `2` distinct `Φ`-points (the `11 + 1` split), so its
line is supported on `s = 2` points. GS then needs divisibility `s·m > D` (i.e. `D < 2m`), while a
nonzero multiplicity-`m` interpolant over the `≤ |κ| = 64` distinct plane points needs
`(D+1)(D+2) > 64·m(m+1)` (coefficients over vanishing constraints) — incompatible for EVERY `m ≥ 1, D`,
via the general `ForMathlib.GuruswamiSudan.gs_interp_window_empty` at `n = |κ| = 64`. So the polynomial
method certifies no list bound at the deployed multiplicity regime; in particular it does not reach
`128`. -/
theorem wrap_gs_interior_window_empty (m D : ℕ) (hm : 1 ≤ m) (hdiv : D < 2 * m) :
    ¬ ((D + 1) * (D + 2) > Fintype.card (Fin (2 ^ 6)) * (m * (m + 1))) := by
  have h : Fintype.card (Fin (2 ^ 6)) = 64 := by simp
  rw [h]
  exact Dregg2.ForMathlib.GuruswamiSudan.gs_interp_window_empty 64 m D (by norm_num) hm hdiv

/-! ## §8. BEYOND JOHNSON — the near-capacity radius `dOut = 125` (`δ ≈ 0.977`), via the DIRECT
PAIR-INJECTION, and the DEPLOYED per-fold soundness over the extension field.

`§3b`–`§7` live AT / just inside the folded code's Johnson radius (`dIn = 56`/`52`), where the
per-`α` agreement floor is `|κ| − dIn = 8`/`12` and the list is `292`/`186`. This section pushes the
OUTER radius all the way to `dOut = 125` — relative `δ = 125/128 ≈ 0.977`, essentially at CAPACITY —
and pairs it with the sharpest inner radius `dIn = 62` (agreement floor `|κ| − dIn = 2`).

At this radius the far-fiber bound COLLAPSES to `≤ 1`: a `125`-far word has, for every constant point
`(a,b)`, at most `(128 − 125 − 1)/2 = 1` fibre on which `(E f, O f) = (a, b)` (`wrap_fiber_le_one`,
from `far_fiber_card` at `dOut = 125`). With `M = 1` the Cauchy–Schwarz/Fisher packing quadratic of
`§F` does NOT bite (`a² = (64 − 62)² = 4 < 64·1 = |κ|·M`), so the list bound is NOT `a²/(a² − nM)`.
Instead it comes from a NEW ELEMENTARY injection:

  each good `α` folds `f` to a constant on `S α` with `|S α| ≥ |κ| − 62 = 2`; for distinct good
  `α ≠ γ` the `2×2` Vandermonde in `(α, γ)` pins any common fibre to a SINGLE `Φ`-value `(a*, b*)`,
  so `S α ∩ S γ ⊆ Φ⁻¹(a*, b*)` has card `≤ M = 1`. Hence a chosen UNORDERED PAIR `{y₁, y₂} ⊆ S α`
  is a well-defined injection `Good ↪ {2-subsets of κ}` (a shared pair would force
  `|S α ∩ S γ| ≥ 2 > 1`). Therefore `|Good| ≤ C(64, 2) = 2016` — an UNCONDITIONAL COUNTING fact.

This is SOUND against Kambiré's capacity refutation: his `n^C` blow-up needs `n → ∞`, `r > 2`, and at
our tiny FIXED dimension-`2` (`r = 2`) code his own construction caps at exactly `C(n, 2)`; no
construction beats a valid counting bound, and `2016 = C(64, 2)` IS that bound here. The count lands
in `κ × κ` and is therefore FIELD-INDEPENDENT — its only field dependence is the soundness DENOMINATOR
`|F_challenge|`. Over the deployed quartic extension field `F = BabyBear⁴`,
`|F| = babyBearP⁴ ≈ 2^123.6`, the per-fold error `|Good|/|F| ≤ 2016/babyBearP⁴ < 2⁻¹¹² ≈ 2⁻¹¹²·⁶`
(`wrap_perFold_soundness_capacity`). No `sorry`, no hypothesis; `fSqWrap` is `125`-far, so it FIRES. -/

/-- **THE FAR-FIBER BOUND COLLAPSES TO `≤ 1` at the near-capacity radius.** A `125`-far word has, for
every constant pair `(a, b)`, at most `1` fibre on which `(E f, O f) = (a, b)`:
`2·|Φ⁻¹(a,b)| + 125 < 128` forces `|Φ⁻¹(a,b)| ≤ 1`. This is `M = 1` — the packing quadratic's death
(`§F`) and the pair-injection's life. -/
theorem wrap_fiber_le_one {f : Fin (2 ^ 7) → BabyBear}
    (hfar : farN friSetupWrapRate.C 125 f) (a b : BabyBear) :
    (Finset.univ.filter (fun y : Fin (2 ^ 6) =>
        E friSetupWrapRate.geom f y = a ∧ O friSetupWrapRate.geom f y = b)).card ≤ 1 := by
  have h := far_fiber_card friSetupWrapRate hfar (wrap_point_mem_C a b)
  have hcard : Fintype.card (Fin (2 ^ 7)) = 128 := by simp
  rw [hcard] at h
  omega

/-- **THE CAPACITY GOOD-CHALLENGE COUNT — the DIRECT PAIR-INJECTION `Good ↪ {2-subsets of κ}`.**
A word `125`-far from the deployed code has at most `C(64, 2) = 2016` folding challenges whose fold is
`62`-close to the constants.

*Proof (elementary, no packing quadratic).* Each good `α` picks a constant `cw α` with agreement set
`S α = {y | E f y + α·O f y = cw α}` of card `≥ |κ| − 62 = 2`. For distinct good `α ≠ γ`, a common
`y ∈ S α ∩ S γ` solves the `2×2` Vandermonde `[[1,α],[1,γ]]` (det `γ − α ≠ 0`) to the SINGLE point
`(a*, b*) = (cw α − α·b*, (cw α − cw γ)/(α − γ))`, so `S α ∩ S γ ⊆ Φ⁻¹(a*, b*)`, of card `≤ 1`
(`wrap_fiber_le_one`). Choosing a `2`-subset `P α ⊆ S α` therefore gives an INJECTION into the
`2`-subsets of `κ`: if `P α = P γ` for `α ≠ γ` then `P α ⊆ S α ∩ S γ` has `2 ≤ 1` elements, absurd.
`|Good| ≤ |{2-subsets of Fin 64}| = C(64, 2) = 2016`. -/
theorem wrap_good_challenge_card_le_capacity {f : Fin (2 ^ 7) → BabyBear}
    (hfar : farN friSetupWrapRate.C 125 f)
    (Good : Finset BabyBear)
    (hGood : ∀ α ∈ Good, closeN friSetupWrapRate.C' 62 (Fold friSetupWrapRate.geom α f)) :
    Good.card ≤ 2016 := by
  classical
  set G := friSetupWrapRate.geom with hG
  -- Each good challenge has a constant witness `cw α` with `≤ 62` disagreements.
  have hex : ∀ α ∈ Good, ∃ c : BabyBear,
      (disagree (Fold G α f) (fun _ => c)).card ≤ 62 := by
    intro α hα
    obtain ⟨g, hgC, hgcard⟩ := hGood α hα
    obtain ⟨c, rfl⟩ := mem_wrap_C'.mp hgC
    exact ⟨c, hgcard⟩
  choose! cw hcw using hex
  -- The agreement sets of the family.
  set Sfun : BabyBear → Finset (Fin (2 ^ 6)) :=
    fun α => Finset.univ.filter (fun y => Fold G α f y = cw α) with hSfun
  -- (i) Each has `≥ 2` points (`64 − 62`).
  have hlow : ∀ α ∈ Good, 2 ≤ (Sfun α).card := by
    intro α hα
    have hcompl : Sfun α = (disagree (Fold G α f) (fun _ => cw α))ᶜ := by
      ext y
      simp [hSfun, disagree]
    have hcc : (Sfun α).card
        = Fintype.card (Fin (2 ^ 6)) - (disagree (Fold G α f) (fun _ => cw α)).card := by
      rw [hcompl, Finset.card_compl]
    have hn : Fintype.card (Fin (2 ^ 6)) = 64 := by simp
    have := hcw α hα
    omega
  -- (ii) Distinct good challenges share `≤ 1` point: their lines meet in ONE point of `F²`.
  have hpair : ∀ α ∈ Good, ∀ γ ∈ Good, α ≠ γ → (Sfun α ∩ Sfun γ).card ≤ 1 := by
    intro α hα γ hγ hne
    have hsub : α - γ ≠ 0 := sub_ne_zero.mpr hne
    refine le_trans (Finset.card_le_card ?_)
      (wrap_fiber_le_one hfar (cw α - α * ((cw α - cw γ) / (α - γ)))
        ((cw α - cw γ) / (α - γ)))
    intro y hy
    rw [Finset.mem_inter, hSfun] at hy
    obtain ⟨hyα, hyγ⟩ := hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hyα hyγ
    have e1 : E G f y + α * O G f y = cw α := hyα
    have e2 : E G f y + γ * O G f y = cw γ := hyγ
    have hO : O G f y = (cw α - cw γ) / (α - γ) := by
      rw [eq_div_iff hsub]
      linear_combination e1 - e2
    have hE : E G f y = cw α - α * ((cw α - cw γ) / (α - γ)) := by
      rw [← hO]
      linear_combination e1
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hE, hO⟩
  -- (iii) THE INJECTION. Pick a `2`-subset `P α ⊆ S α`; distinct good `α` give distinct subsets
  -- because a shared subset would sit in `S α ∩ S γ` (card `≤ 1`), impossible at card `2`.
  have hPex : ∀ α ∈ Good, ∃ t : Finset (Fin (2 ^ 6)), t ⊆ Sfun α ∧ t.card = 2 := by
    intro α hα
    obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq (hlow α hα)
    exact ⟨t, hts, htc⟩
  choose! P hPsub hPcard using hPex
  have hmemP : ∀ α ∈ Good,
      P α ∈ Finset.powersetCard 2 (Finset.univ : Finset (Fin (2 ^ 6))) := by
    intro α hα
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, hPcard α hα⟩
  have hinj : Set.InjOn P ↑Good := by
    intro α hα γ hγ hPeq
    rw [Finset.mem_coe] at hα hγ
    by_contra hne
    have hsubInt : P α ⊆ Sfun α ∩ Sfun γ := by
      intro y hy
      rw [Finset.mem_inter]
      refine ⟨hPsub α hα hy, ?_⟩
      rw [hPeq] at hy
      exact hPsub γ hγ hy
    have h2 : 2 ≤ (Sfun α ∩ Sfun γ).card :=
      le_trans (le_of_eq (hPcard α hα).symm) (Finset.card_le_card hsubInt)
    have h1 := hpair α hα γ hγ hne
    omega
  calc Good.card
      ≤ (Finset.powersetCard 2 (Finset.univ : Finset (Fin (2 ^ 6)))).card :=
        Finset.card_le_card_of_injOn P hmemP hinj
    _ = 2016 := by
        rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
        decide

/-- **THE CAPACITY WITNESS — `BadChallengePoly friSetupWrapRate 125 62 2016`.** For a `125`-far `f`
the good set has card `≤ 2016` (`wrap_good_challenge_card_le_capacity`), so `∏_{α good}(X − C α)` is
the nonzero degree-`≤ 2016` witness vanishing on every good challenge — the beyond-Johnson (near
CAPACITY, `dOut = 125`) proximity-gap witness. No `sorry`, no hypothesis. -/
theorem wrap_badChallengePoly_capacity :
    BadChallengePoly friSetupWrapRate 125 62 2016 := by
  classical
  intro f hfar
  set Gd : Set BabyBear :=
    {α : BabyBear | closeN friSetupWrapRate.C' 62 (Fold friSetupWrapRate.geom α f)} with hGd
  have hfin : Gd.Finite := Set.toFinite _
  set Good : Finset BabyBear := hfin.toFinset with hGood
  have hmem : ∀ α, α ∈ Good ↔ α ∈ Gd := by
    intro α; rw [hGood]; simp only [Set.Finite.mem_toFinset]
  have hcard : Good.card ≤ 2016 :=
    wrap_good_challenge_card_le_capacity hfar Good (fun α hα => (hmem α).mp hα)
  refine ⟨∏ α ∈ Good, (X - C α),
    (monic_prod_X_sub_C (fun α : BabyBear => α) Good).ne_zero, ?_, ?_⟩
  · rw [natDegree_finsetProd_X_sub_C_eq_card Good (fun α : BabyBear => α)]
    exact hcard
  · intro α hα
    have hαG : α ∈ Good := (hmem α).mpr hα
    show (∏ β ∈ Good, (X - C β)).eval α = 0
    rw [eval_prod]
    exact Finset.prod_eq_zero hαG (by simp)

/-- **THE CAPACITY PROXIMITY GAP — `FriProximityGapChallenges friSetupWrapRate 125 62 2016`,
unconditional.** A `125`-far word (relative `δ ≈ 0.977`, near capacity) has at most `2016 = C(64,2)`
folding challenges whose fold is `62`-close to the constants — the direct pair-injection count, routed
through `friProximityGap_of_badChallengePoly`. No hypothesis remains. -/
theorem wrap_friProximityGap_capacity :
    FriProximityGapChallenges friSetupWrapRate 125 62 2016 :=
  friProximityGap_of_badChallengePoly friSetupWrapRate 125 62 2016 wrap_badChallengePoly_capacity

/-- **`fSqWrap` is `125`-FAR from the deployed code.** It agrees with every codeword on `≤ 2` of `128`
points (`fSqWrap_agree_le_two`), so disagrees on `≥ 126 > 125` — supplying the far hypothesis of the
capacity witness NON-VACUOUSLY (`125 + 2 = 127 < 128`). -/
theorem fSqWrap_far_125 : farN friSetupWrapRate.C 125 fSqWrap := by
  refine farN_of_agree_le (k := 2) ?_ fSqWrap_agree_le_two
  have hn : Fintype.card (Fin (2 ^ 7)) = 128 := by simp
  rw [hn]
  norm_num

/-- **The capacity gap FIRES on the concrete `125`-far `fSqWrap`, unconditionally**: at most `2016`
folding challenges fold it `62`-close to the constants, exhibited as the roots of an actual nonzero
polynomial of degree `≤ 2016`. Non-vacuous — `fSqWrap_far_125` supplies the far hypothesis. -/
theorem wrap_capacity_witness_fires :
    ∃ P : BabyBear[X], P ≠ 0 ∧ P.natDegree ≤ 2016 ∧
      {α : BabyBear | closeN friSetupWrapRate.C' 62 (Fold friSetupWrapRate.geom α fSqWrap)}
        ⊆ {α : BabyBear | P.eval α = 0} :=
  wrap_badChallengePoly_capacity fSqWrap_far_125

/-- **THE DEPLOYED PER-FOLD SOUNDNESS, over the extension-field challenge domain.** The capacity
good-challenge count `≤ 2016 = C(64,2)` is FIELD-INDEPENDENT — the injection lands in the unordered
pairs of the `64`-point folded DOMAIN `κ`, not in the challenge field — so the SAME count holds when
folding challenges are drawn from the deployed quartic extension field `F = BabyBear⁴`
(`|F| = babyBearP⁴ ≈ 2^123.6`). The per-fold proximity-gap soundness error is then
`|Good| / |F| ≤ 2016 / babyBearP⁴`, and THIS theorem's own conclusion is that this density is
`< 1/2¹¹² = 2⁻¹¹²` — i.e. **`≥ 112` proven bits** for the deployed extension field. (The exact value
is `≈ 2⁻¹¹²·⁶⁵`, strictly inside `(2⁻¹¹³, 2⁻¹¹²)` per `wrap_perFold_soundness_capacity_interval`; the
`~113`-bit figure rounds `123.6 − 11 = 112.6`. `2⁻¹¹³` is NOT a valid upper bound — the honest bound
is `2⁻¹¹²`.) -/
theorem wrap_perFold_soundness_capacity {f : Fin (2 ^ 7) → BabyBear}
    (hfar : farN friSetupWrapRate.C 125 f) (Good : Finset BabyBear)
    (hGood : ∀ α ∈ Good, closeN friSetupWrapRate.C' 62 (Fold friSetupWrapRate.geom α f)) :
    (Good.card : ℝ) / (babyBearP : ℝ) ^ 4 < 1 / 2 ^ 112 := by
  have hc : Good.card ≤ 2016 := wrap_good_challenge_card_le_capacity hfar Good hGood
  have hcR : (Good.card : ℝ) ≤ 2016 := by exact_mod_cast hc
  have hpval : (babyBearP : ℝ) = 2013265921 := by norm_num [babyBearP]
  rw [hpval]
  have hden : (0 : ℝ) < (2013265921 : ℝ) ^ 4 := by norm_num
  have h2 : (0 : ℝ) < (2 : ℝ) ^ 112 := by positivity
  rw [div_lt_div_iff₀ hden h2, one_mul]
  have key : (2016 : ℝ) * 2 ^ 112 < (2013265921 : ℝ) ^ 4 := by norm_num
  nlinarith [hcR, h2, key]

/-- **The exact soundness interval — `2⁻¹¹³ < 2016/babyBearP⁴ < 2⁻¹¹²`.** The deployed per-fold error
is strictly between `2⁻¹¹³` and `2⁻¹¹²` (`≈ 2⁻¹¹²·⁶⁵`): `2016·2¹¹² < babyBearP⁴ < 2016·2¹¹³`. This
pins the HONEST bit-count at `~112.6` — the proven guarantee is `≥ 112` bits (the `2⁻¹¹²` upper bound),
NOT the rounded `113`. -/
theorem wrap_perFold_soundness_capacity_interval :
    2016 * 2 ^ 112 < babyBearP ^ 4 ∧ babyBearP ^ 4 < 2016 * 2 ^ 113 := by
  refine ⟨?_, ?_⟩ <;> norm_num [babyBearP]

/-! ## §4. Axiom hygiene. -/

#assert_axioms wrap_fiber_le_one
#assert_axioms wrap_good_challenge_card_le_capacity
#assert_axioms wrap_badChallengePoly_capacity
#assert_axioms wrap_friProximityGap_capacity
#assert_axioms fSqWrap_far_125
#assert_axioms wrap_capacity_witness_fires
#assert_axioms wrap_perFold_soundness_capacity
#assert_axioms wrap_perFold_soundness_capacity_interval
#assert_axioms correlatedAgreementLine_twoPoint
#assert_axioms correlatedAgreementLineAt_twoPoint
#assert_axioms wrap_good_challenge_card_le_sharp
#assert_axioms sharp_of_correlatedAgreementLine
#assert_axioms wrap_friProximityGap_sharp
#assert_axioms wrap_sharp_witness_fires
#assert_axioms wrap_correlatedAgreementLine
#assert_axioms wrap_correlatedAgreement_sharp_proved
#assert_axioms wrap_friProximityGap_sharp_proved
#assert_axioms wrap_sharp_witness_fires_proved
#assert_axioms wrap_below_gs_line_radius
#assert_axioms wrap_meets_gs_line_radius
#assert_axioms wrap_correlatedAgreementLine_interior
#assert_axioms wrap_good_challenge_card_le_interior
#assert_axioms interior_of_correlatedAgreementLine
#assert_axioms wrap_friProximityGap_interior
#assert_axioms wrap_badChallengePoly_interior_proved
#assert_axioms wrap_friProximityGap_interior_proved
#assert_axioms wrap_interior_witness_fires_proved
#assert_axioms wrap_gs_weighted_denominator_negative
#assert_axioms wrap_gs_interior_window_empty

end Dregg2.Circuit.FriCorrelatedAgreementSharp

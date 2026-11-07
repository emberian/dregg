/-
# `Dregg2.Circuit.FriPositiveRadiusSchedule` — ⚑ THE POSITIVE-RADIUS SCHEDULE, and the precise
reason the FIXED-code `ChainStepGap` cannot carry one.

`FriFoldConsistencyDichotomy` composed FS survival with query payment into
`strategy_soundness_compose` and left exactly ONE named residual: `ChainStepGap C rad d goodSet
fold` — "a `rad`-far word folded at a challenge outside its good set is `(rad+d)`-far" — with the
note that what blocks an instance is that every landed schedule runs at `d = 0`. This file settles
the radius question. Read §1 FIRST: the answer is not "here is the instance".

## §1 — ⚑ THE SHAPE IS WRONG, and that is a THEOREM, not a difficulty

State the trap first, because it is easy to "land" the residual and mean nothing by it: a
`ChainStepGap C rad d goodSet fold` instance at `d > 0` is FREE. Take the by-definition good set
`{ρ | ¬ farN C (rad+d) (fold w ρ)}` and the predicate holds at EVERY margin, at every domain,
for every fold (`chainStepGap_free`). So the residual's content was never the predicate — it is
the CAP `b` on that good set, which is what `strategy_soundness_compose` actually spends
(`hE : ∀ dd, (E dd).card ≤ b`, paying `n·b/|R|`). The tree already says this about the sibling
object: `FriChainStepIdx.goodSet_by_definition_is_free`.

And THE CAP is what cannot be had at a fixed radius. `ChainStepGap` fixes ONE code `C` and ONE
radius `rad` and demands the fold land at `rad + d` — the fold must GAIN `d` of
distance-to-code. Both proximity laws in the tree make it LOSE distance by a fixed factor, and
each is exactly the hypothesis under which the corresponding cap is proved:

  * `FriChainStepIdx.goodδ_card_lt` (CA-free, BBHR18 Vandermonde): the cap `< n` needs the source
    word `n²·d`-far to cap the `d`-good set — a factor `n² = 64` at the deployed arity.
  * `CorrelatedAgreement.Interface.towerGood_card_le` (the CA route): the cap `(m−1)(r+1)` needs
    the constant-RELATIVE-radius law `m·rᵢ₊₁ ≤ rᵢ` — a factor `m = 8`.

Reading `ChainStepGap` as a schedule, it is the CONSTANT schedule `rᵢ ≡ rad` with margin `d`, so
either cap hypothesis reads `c·(rad + d) ≤ rad` with `c ≥ 1`, which is FALSE for `d ≥ 1`
(`constant_radius_margin_infeasible`). So there is no CAPPED `ChainStepGap` instance at `d > 0`
under either proximity law — not at `|ι| = 16`, not at `2^19`, not at any domain, and no bigger
domain fixes it. It is not a missing lemma; the radius has to be allowed to FALL.

And the CA-free `n²` law cannot carry a positive radius at the deployed five-layer `2^19` tower
even with `d = 0`: `rad₀ ≥ 64⁵ = 2³⁰` while every word of `Fin (2^19) → BabyBear` is within
`2^19` of the zero codeword, so layer-0 farness is UNINHABITED there
(`deployed_n2_positive_radius_impossible`, `deployed_n2_positive_margin_impossible`). This is
proved from `Finset.card_le_univ` alone — no covering-radius theory needed.

## §2 — WHAT THE `2^19` TOWER CAN ACTUALLY SUPPORT

The CA route's law is `m·rᵢ₊₁ ≤ rᵢ` at `m = 8`, and the domain shrinks by 8 per layer, so a
CONSTANT RELATIVE radius survives all five welded layers — that is exactly
`CorrelatedAgreement.Theorems.towerRR i = 8^(5−i)`, which is TIGHT (`8·rᵢ₊₁ = rᵢ` at every rung)
and therefore has NO room for a margin. §2 opens the room: `mRR` satisfies the MARGIN law
`8·(mRRᵢ₊₁ + 1) ≤ mRRᵢ` at all five layers while staying inside the classical CA regime
`9·(mRRᵢ₊₁ + 1) + kᵢ₊₁ ≤ nᵢ₊₁` at every layer, and layer-0 farness at `mRR 0 = 37448` is
INHABITED by the tower's own `farWord` (the degree-`2^16` monomial, `2^19 − 2^16 = 458752`-far).
Slack `1` is the CEILING at depth 5: layer 5's classical regime is `9r + 2 ≤ 16`, so
`r₅ + d ≤ 1`; hence `mRR 5 = 0` and the TERMINAL farness of the depth-5 ladder is "not a
codeword", with layers 0–4 at genuinely positive radii `37448, 4680, 584, 72, 8`. A larger margin
costs depth, and §4 spends that trade deliberately.

## §3 — THE LADDER-GRADED OBLIGATION, DISCHARGED

`ChainStepGapLadder` is `ChainStepGap` with the radius allowed to fall: source radius `rᵢ` at
code `Vᵢ`, target radius `rᵢ₊₁ + d` at code `Vᵢ₊₁`. Like `ChainStepGap` (and like
`FriChainStepIdx.goodδ`) it is FREE once the good set is by-definition — the content is the CAP,
and the cap here is `goodMargin_card_le`, proved from the landed per-layer CA
(`CorrelatedAgreementCurveUDParam`) and the landed decimation-lift weld (`DecimLift`), with NO new
hypothesis. `chainStepSlackLadder` is then the Hamming-triangle step the slackened chain consumes
— the ladder form of `FriFoldConsistencyDichotomy.chainStepSlack_of_gap`.

## §4 — ⚑ THE COMPOSED BOUND AT THE DEPLOYED `2^19` TOWER, BOTH ADDENDS MEANINGFUL

`compose_one_round` is `strategy_soundness_compose`'s statement with the radius allowed to FALL
across the round: for an ARBITRARY round-1 commitment `S : F → (Fin n₁ → F)` — no
fold-consistency gate in the statement — the joint probability (random oracle × query sample)
that farness dies AND the fold-consistency spot check passes is at most `b/|F| + (1−δ)^k`. Same
two-branch proof (`winProb_le_add`, `winProb_fst`, `winProb_le_of_fiber`, `accept_prob_le`),
same landed lemmas; what changes is that the surviving-farness radius at round 1 is `r₁`, not
`r₀`, which is what the fold law actually gives.

At the deployed tower, layer 0 → layer 1 of `FriSetupTower.towerS`: `r₀ = 50968`,
`r₁ = 2275`, margin `d = 4096` (so `r₁ + d = 6371`, `8·(r₁+d) = r₀` exactly, and the classical
CA regime `9·(r₁+d) + 2^13 = 65531 ≤ 2^16` holds with 5 to spare), cap `b = 7·6372 = 44604`,
`δ = 1/16` (admissible because `δ·2^16 = 4096 = d`), `k = 38`:

    44604/|BabyBear| + (15/16)^38  <  1        (`deployed_compose_lt_one`)

with `44604/2013265921 ≈ 2.2·10⁻⁵` and `(15/16)^38 ≈ 0.0861`. BOTH addends are real: the FS
addend is a genuine CA-capped bad-set mass, the query addend a genuine sub-1 spot-check mass.
The far hypothesis is INHABITED (`farWord_far_compose`, radius `50968`), which is exactly what
fails at `|ι| = 16` (`FriPositiveRadiusPayment.positive_radius_payment_vacuous_at_friSetupK8`),
and the SURVIVING radius at layer 1 is `2275` (relative `≈ 3.5%` of the `2^16` domain) — positive,
not the degenerate `0`.

⚑ The margin and the surviving radius trade against each other inside ONE budget
`r₁ + d ≤ 6371`: every point of slack handed to the spot check is a point of surviving radius
given up. `δ = 1/16` is what fixes the split here; a larger `δ` buys a smaller `(1−δ)^k` at a
smaller `r₁`.

## What this does NOT say (read before quoting the number)

  * ONE round. The query branch's sample lives on the layer-1 domain `Fin (2^16)`; a
    multi-round version needs a per-layer sample space, which is NOT built here.
  * It does not bind the commitment (no Merkle/extractor), the query model is the uniform
    i.i.d. idealization (`FriQuerySamplingBias` records the deployed sampler is not that), and
    the FS branch prices the ROM challenge, not the deployed transcript.
  * It moves no deployed statement and discharges no FRI/STARK floor. ADDITIVE only.

## Rooting
NOT imported by `Dregg2.lean` — it needs one `import Dregg2.Circuit.FriPositiveRadiusSchedule`
line added there (deliberately not edited: concurrent lanes).

## Axiom hygiene
`#assert_all_clean` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`, no fresh `axiom`, no
`native_decide`. ADDITIVE: no existing module is edited.
-/
import Dregg2.Circuit.FriFoldConsistencyDichotomy
import Dregg2.Circuit.CorrelatedAgreement.Theorems
import Dregg2.Tactics
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Dregg2.Circuit.FriPositiveRadiusSchedule

open Dregg2.Circuit.CorrelatedAgreement
open Dregg2.Circuit.CorrelatedAgreement.Interface
open Dregg2.Circuit.CorrelatedAgreement.DecimLiftDischarge (towerV towerDec decimLift_of_tower)
open Dregg2.Circuit.FriSetupTower (twSz towerS wchain wchain_ord monoW farWord
  pow_inj_of_orderOf)
open Dregg2.Circuit.BabyBearFriField (BabyBear)
open Dregg2.Crypto.ProbCrypto (winProb)
open Dregg2.Crypto.RomOracle (OracleComp QueryBounded)
open Dregg2.Circuit.FriChainStepIdx (hitWin hitWin_pure hitWin_query hit_bound)
open Dregg2.Circuit.FriQuerySoundness (Accepts accept_prob_le)
open Dregg2.Circuit.FriSoundness (disagree)
open Dregg2.Circuit.FriFoldConsistencyDichotomy (winProb_le_add winProb_fst winProb_le_of_fiber)

/-! ## §1 — ⚑ THE OBSTRUCTION: a FIXED-radius `ChainStepGap` cannot be CAPPED at `d > 0`. -/

open Classical in
/-- **⚑ `ChainStepGap` AT `d > 0` IS FREE — so landing "an instance" means NOTHING on its own.**
At the by-definition good set `{ρ | the fold is NOT (rad+d)-far}` the predicate holds at every
margin `d`, every code, every radius, every fold — no proximity math involved. What
`strategy_soundness_compose` actually consumes is not this predicate but a CAP `b` on the good
set (`hE`, paying `n·b/|R|`), and §1's real content is that no such cap exists at `d > 0`. The
tree already records the same trap for the sibling object
(`FriChainStepIdx.goodSet_by_definition_is_free`). -/
theorem chainStepGap_free {F : Type} [Field F] [DecidableEq F] {ι : Type} [Fintype ι]
    [DecidableEq ι] {R : Type} [Fintype R] [DecidableEq R]
    (C : Submodule F (ι → F)) (rad d : ℕ) (fold : (ι → F) → R → (ι → F)) :
    Dregg2.Circuit.FriFoldConsistencyDichotomy.ChainStepGap C rad d
      (fun w => Finset.univ.filter fun ρ =>
        ¬ Dregg2.Circuit.FriSoundness.farN C (rad + d) (fold w ρ)) fold := by
  intro w ρ _ hρ
  by_contra hc
  exact hρ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)

/-- **⚑ THE SHAPE OBSTRUCTION, as arithmetic.** `ChainStepGap C rad d goodSet fold` reads, as a
radius schedule, the CONSTANT schedule `rᵢ ≡ rad` carrying a margin `d`. Both proximity laws in
the tree prove their good-set CAP only under "the source radius is at least `c` times the target
radius", with `c = m = 8` (correlated agreement, `Interface.towerGood_card_le`) or `c = n² = 64`
(BBHR18 Vandermonde, `FriChainStepIdx.goodδ_card_lt`). At a constant schedule with margin that
hypothesis reads `c·(rad + d) ≤ rad`, which is FALSE for every `c ≥ 1` and `d ≥ 1`. So the
residual `ChainStepGap` at `d > 0` is not a missing lemma at a bigger domain — it is the wrong
shape, and the radius has to be allowed to FALL (§3). -/
theorem constant_radius_margin_infeasible {c rad d : ℕ} (hc : 1 ≤ c) (hd : 1 ≤ d) :
    ¬ (c * (rad + d) ≤ rad) := by
  intro h
  have hle : rad + d ≤ c * (rad + d) := Nat.le_mul_of_pos_left _ hc
  omega

/-- Every word is `Fintype.card ι`-close to any code containing `0`: farness at a radius that
reaches the domain size is UNINHABITED. (`Finset.card_le_univ`; no covering-radius theory.) -/
theorem closeN_of_card_le {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F] [DecidableEq F]
    {V : Set (ι → F)} (h0 : (0 : ι → F) ∈ V) {r : ℕ} (hr : Fintype.card ι ≤ r) (w : ι → F) :
    closeN V r w := by
  refine ⟨0, h0, ?_⟩
  refine le_trans ?_ hr
  simpa [hammingDist] using Finset.card_le_univ (Finset.univ.filter fun i => w i ≠ (0 : ι → F) i)

/-- **The `n²` law forces an absurd top radius over five layers, WITH a margin.** Five rungs of
`64·(rᵢ₊₁ + d) ≤ rᵢ` at `d ≥ 1` push `r₀` past `2^19` — past the whole deployed domain. -/
theorem n2_margin_forces_huge_top {RR : ℕ → ℕ} {d : ℕ} (hd : 1 ≤ d)
    (hs : ∀ i, i < 5 → 64 * (RR (i + 1) + d) ≤ RR i) : 2 ^ 19 ≤ RR 0 := by
  have h0 := hs 0 (by omega)
  have h1 := hs 1 (by omega)
  have h2 := hs 2 (by omega)
  have h3 := hs 3 (by omega)
  have h4 := hs 4 (by omega)
  norm_num at h0 h1 h2 h3 h4 ⊢
  omega

/-- **The `n²` law forces an absurd top radius over five layers, even at ZERO margin**, as soon
as the BOTTOM radius is positive: `r₀ ≥ 64⁵ = 2³⁰`. -/
theorem n2_forces_huge_top {RR : ℕ → ℕ} (h5 : 1 ≤ RR 5)
    (hs : ∀ i, i < 5 → 64 * RR (i + 1) ≤ RR i) : 2 ^ 19 ≤ RR 0 := by
  have h0 := hs 0 (by omega)
  have h1 := hs 1 (by omega)
  have h2 := hs 2 (by omega)
  have h3 := hs 3 (by omega)
  have h4 := hs 4 (by omega)
  norm_num at h0 h1 h2 h3 h4 ⊢
  omega

/-- The zero word is a layer-0 codeword of the deployed tower. -/
theorem zero_mem_towerV0 : (0 : Fin (twSz 0) → BabyBear) ∈ towerV 0 :=
  (towerS 0 (by omega)).C.zero_mem

/-- **⚑ THE CA-FREE `n²` SCHEDULE IS DEAD AT THE DEPLOYED TOWER (positive radius).** There is no
radius schedule obeying the BBHR18-Vandermonde law `64·rᵢ₊₁ ≤ rᵢ` across the five welded `2^19`
layers with a POSITIVE bottom radius and an INHABITED layer-0 farness: the law forces
`r₀ ≥ 2^30`, and no word of `Fin (2^19) → BabyBear` is `2^19`-far from the layer-0 code. -/
theorem deployed_n2_positive_radius_impossible :
    ¬ ∃ RR : ℕ → ℕ, 1 ≤ RR 5 ∧ (∀ i, i < 5 → 64 * RR (i + 1) ≤ RR i) ∧
        ∃ w : Fin (twSz 0) → BabyBear, ¬ closeN (towerV 0) (RR 0) w := by
  rintro ⟨RR, h5, hs, w, hw⟩
  refine hw (closeN_of_card_le zero_mem_towerV0 ?_ w)
  have := n2_forces_huge_top h5 hs
  simpa [twSz] using this

/-- **⚑ AND IT IS DEAD WITH A MARGIN TOO.** Same statement with the margin law
`64·(rᵢ₊₁ + d) ≤ rᵢ`, `d ≥ 1` — the shape `ChainStepGap` needs. So the CA-free route cannot
supply a positive-margin instance at the deployed tower at ANY bottom radius, including `0`. -/
theorem deployed_n2_positive_margin_impossible :
    ¬ ∃ (RR : ℕ → ℕ) (d : ℕ), 1 ≤ d ∧ (∀ i, i < 5 → 64 * (RR (i + 1) + d) ≤ RR i) ∧
        ∃ w : Fin (twSz 0) → BabyBear, ¬ closeN (towerV 0) (RR 0) w := by
  rintro ⟨RR, d, hd, hs, w, hw⟩
  refine hw (closeN_of_card_le zero_mem_towerV0 ?_ w)
  have := n2_margin_forces_huge_top hd hs
  simpa [twSz] using this

/-! ## §2 — the MARGIN schedule the `2^19` tower does support. -/

/-- **⚑ THE FIVE-LAYER MARGIN SCHEDULE.** `CorrelatedAgreement.Theorems.towerRR i = 8^(5−i)` is
TIGHT (`8·rᵢ₊₁ = rᵢ` at every rung), so it has no room for a margin. `mRR` keeps the
constant-relative-radius law but leaves `1` of slack at every rung — the ceiling at depth 5,
since layer 5's classical CA regime `9r + 2 ≤ 16` allows only `r ≤ 1`. -/
def mRR : ℕ → ℕ
  | 0 => 37448
  | 1 => 4680
  | 2 => 584
  | 3 => 72
  | 4 => 8
  | _ + 5 => 0

/-- **The margin law holds at all five welded layers**: `8·(mRRᵢ₊₁ + 1) ≤ mRRᵢ`. -/
theorem mRR_margin : ∀ i, i < 5 → 8 * (mRR (i + 1) + 1) ≤ mRR i := by
  intro i hi
  interval_cases i <;> norm_num [mRR]

/-- The plain constant-relative-radius law (what the landed `towerE_card_le` consumes). -/
theorem mRR_sched : ∀ i, 8 * mRR (i + 1) ≤ mRR i := by
  intro i
  match i with
  | 0 => norm_num [mRR]
  | 1 => norm_num [mRR]
  | 2 => norm_num [mRR]
  | 3 => norm_num [mRR]
  | 4 => norm_num [mRR]
  | n + 5 => show 8 * mRR (n + 1 + 5) ≤ mRR (n + 5); norm_num [mRR]

/-- **⚑ THE MARGIN RADIUS IS INSIDE THE CLASSICAL CA REGIME AT EVERY LAYER.** `9·r + kᵢ ≤ nᵢ` at
`r = mRRᵢ₊₁ + 1` reads `42129+8192 ≤ 65536`, `5265+1024 ≤ 8192`, `657+128 ≤ 1024`,
`81+16 ≤ 128`, `11 ≤ 16` — so the per-layer correlated agreement AT THE MARGIN RADIUS is a
theorem (`curveUDParam_towerLayer`), not an assumption. This is what `towerRR`'s tight schedule
could not give: the margin sits inside the regime at all five welded layers. -/
theorem hCA_margin : ∀ i, i < 5 →
    CorrelatedAgreementCurveUDParam BabyBear (twSz (i + 1)) (towerV (i + 1))
      (mRR (i + 1) + 1) 8 := by
  intro i hi
  interval_cases i
  · exact curveUDParam_towerLayer (N := twSz 1) (D := 2 ^ 13) (r := mRR 1 + 1) (m := 8)
      (wchain 2)
      (by rw [wchain_ord 2 (by norm_num)]; norm_num [twSz]) (by norm_num [twSz])
      (by norm_num) (by omega) (by norm_num [twSz, mRR])
  · exact curveUDParam_towerLayer (N := twSz 2) (D := 2 ^ 10) (r := mRR 2 + 1) (m := 8)
      (wchain 3)
      (by rw [wchain_ord 3 (by norm_num)]; norm_num [twSz]) (by norm_num [twSz])
      (by norm_num) (by omega) (by norm_num [twSz, mRR])
  · exact curveUDParam_towerLayer (N := twSz 3) (D := 2 ^ 7) (r := mRR 3 + 1) (m := 8)
      (wchain 4)
      (by rw [wchain_ord 4 (by norm_num)]; norm_num [twSz]) (by norm_num [twSz])
      (by norm_num) (by omega) (by norm_num [twSz, mRR])
  · exact curveUDParam_towerLayer (N := twSz 4) (D := 2 ^ 4) (r := mRR 4 + 1) (m := 8)
      (wchain 5)
      (by rw [wchain_ord 5 (by norm_num)]; norm_num [twSz]) (by norm_num [twSz])
      (by norm_num) (by omega) (by norm_num [twSz, mRR])
  · exact curveUDParam_towerLayer (N := twSz 5) (D := 2) (r := mRR 5 + 1) (m := 8)
      (wchain 6)
      (by rw [wchain_ord 6 (by norm_num)]; norm_num [twSz]) (by norm_num [twSz])
      (by norm_num) (by omega) (by norm_num [twSz, mRR])

/-- **⚑ LAYER-0 FARNESS AT THE MARGIN SCHEDULE IS INHABITED** — the tower's own degree-`2^16`
monomial is `2^19 − 2^16 = 458752`-far from the layer-0 code, hence `37448`-far. THIS is the
hypothesis that is uninhabitable at the `|ι| = 16` toy
(`FriPositiveRadiusPayment.friSetupK8_no_positive_far_oracle`), and it holds here. -/
theorem farWord_far_margin : ¬ closeN (towerV 0) (mRR 0) farWord := by
  have h : ¬ closeN (RScode (fun x : Fin (twSz 0) => wchain 1 ^ (x : ℕ)) (2 ^ 16) :
      Set (Fin (twSz 0) → BabyBear)) (mRR 0) (fun x => (wchain 1 ^ (x : ℕ)) ^ (2 ^ 16)) :=
    monomial_far (fun a b hab =>
      Fin.ext (pow_inj_of_orderOf
        (by rw [wchain_ord 1 (by norm_num)]; norm_num [twSz]) (by norm_num [twSz])
        a.isLt b.isLt hab))
      (by norm_num [twSz, mRR])
  rw [RScode_eq_towerRsCode (by norm_num)] at h
  exact h

/-! ### §2.1 — the schedule the §4 COMPOSITION spends: one round, a big margin.

Depth and margin trade against each other inside the classical CA regime. `mRR` maximizes DEPTH
(five layers) at slack `1`. `cRR` maximizes MARGIN at depth 1: layer 1's regime is
`9r + 2^13 ≤ 2^16`, i.e. `r ≤ 6371`, so `r₁ + d = 6371` is the ceiling; `r₁ = 1` keeps the
surviving radius POSITIVE and leaves `d = 6370` for the spot check to spend. The fold law is
then exactly tight: `8·6371 = 50968 = cRR 0`. -/

/-- The one-round schedule: top radius `50968`, surviving radius `1`, margin `6370`. -/
def cRR : ℕ → ℕ
  | 0 => 50968
  | _ => 6371

theorem cRR_zero : cRR 0 = 50968 := rfl
theorem cRR_one : cRR 1 = 6371 := rfl

/-- The fold law at the composition schedule, exactly tight. -/
theorem cRR_sched : 8 * cRR 1 ≤ cRR 0 := by norm_num [cRR]

/-- The composition schedule's layer-1 radius is inside the classical CA regime
(`9·6371 + 2^13 = 65531 ≤ 2^16`) — with `5` to spare. -/
theorem hCA_compose :
    CorrelatedAgreementCurveUDParam BabyBear (twSz 1) (towerV 1) (cRR 1) 8 := by
  have h : ∀ i, i < 1 →
      CorrelatedAgreementCurveUDParam BabyBear (twSz (i + 1)) (towerV (i + 1)) (cRR 1) 8 := by
    intro i hi
    interval_cases i
    exact curveUDParam_towerLayer (N := twSz 1) (D := 2 ^ 13) (r := cRR 1) (m := 8) (wchain 2)
      (by rw [wchain_ord 2 (by norm_num)]; norm_num [twSz]) (by norm_num [twSz])
      (by norm_num) (by omega) (by norm_num [twSz, cRR])
  exact h 0 (by omega)

/-- **Layer-0 farness at the composition schedule is INHABITED** (`50968 + 2^16 < 2^19`). -/
theorem farWord_far_compose : ¬ closeN (towerV 0) (cRR 0) farWord := by
  have h : ¬ closeN (RScode (fun x : Fin (twSz 0) => wchain 1 ^ (x : ℕ)) (2 ^ 16) :
      Set (Fin (twSz 0) → BabyBear)) (cRR 0) (fun x => (wchain 1 ^ (x : ℕ)) ^ (2 ^ 16)) :=
    monomial_far (fun a b hab =>
      Fin.ext (pow_inj_of_orderOf
        (by rw [wchain_ord 1 (by norm_num)]; norm_num [twSz]) (by norm_num [twSz])
        a.isLt b.isLt hab))
      (by norm_num [twSz, cRR])
  rw [RScode_eq_towerRsCode (by norm_num)] at h
  exact h

/-! ## §3 — ⚑ THE LADDER-GRADED OBLIGATION, and its CAP. -/

section Ladder

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {nn : ℕ → ℕ} {V : ∀ i, Set (Fin (nn i) → F)} {rr : ℕ → ℕ} {m : ℕ}
variable {dec : ∀ i, (Fin (nn i) → F) → Fin m → (Fin (nn (i + 1)) → F)}

/-- **⚑ `ChainStepGapLadder` — `ChainStepGap` with the radius allowed to FALL.** A word `rᵢ`-far
from the layer-`i` code, folded at a challenge outside its `(rᵢ₊₁ + d)`-good set, is
`(rᵢ₊₁ + d)`-far from the layer-`(i+1)` code — source radius `rᵢ`, target radius `rᵢ₊₁ + d`,
margin `d`. This is the object `FriFoldConsistencyDichotomy.ChainStepGap` should have been: at
`nn ≡ const`, `V ≡ const` and `rr ≡ const` it IS `ChainStepGap`, and §1 proves that specialization
has no instance at `d > 0`. -/
def ChainStepGapLadder (nn : ℕ → ℕ) (V : ∀ i, Set (Fin (nn i) → F)) (rr : ℕ → ℕ) (m : ℕ)
    (dec : ∀ i, (Fin (nn i) → F) → Fin m → (Fin (nn (i + 1)) → F)) (d : ℕ) : Prop :=
  ∀ (i : ℕ) (w : Fin (nn i) → F) (ρ : F),
    ¬ closeN (V i) (rr i) w →
    ρ ∉ towerGood nn V (fun j => rr j + d) m dec i w →
      ¬ closeN (V (i + 1)) (rr (i + 1) + d) (towerFold nn m dec i w ρ)

/-- The ladder obligation holds for the by-definition good set — FREE, exactly as
`ChainStepGap` is free for `goodδ`. ⚑ Stated so it cannot be read up: this carries NO content.
The content is `goodMargin_card_le` below, which CAPS that good set; the tree's own
`FriChainStepIdx.goodSet_by_definition_is_free` is the reason to say so out loud. -/
theorem chainStepGapLadder_holds (d : ℕ) : ChainStepGapLadder nn V rr m dec d :=
  fun _ _ _ _ hρ hclose => hρ (mem_towerGood.mpr hclose)

/-- **⚑ THE CONTENT — THE MARGIN CAP, from the landed CA + lift, with NO new hypothesis.** At a
layer-`i` word that is `rᵢ`-far, at most `(m−1)(rᵢ₊₁ + d + 1)` challenges fold it within
`rᵢ₊₁ + d` of the next layer's code, PROVIDED the margin fold law `m·(rᵢ₊₁ + d) ≤ rᵢ` holds and
the layer's correlated agreement holds AT THE MARGIN RADIUS. Same two-step proof as
`Interface.towerGood_card_le` (CA produces the common agreement set, `DecimLift` lifts it,
`closeN_mono` closes against the source radius) — what is new is that the margin is carried
through, which is what turns the exact gate into a spot-checkable one. -/
theorem goodMargin_card_le {i : ℕ} {w : Fin (nn i) → F} {d : ℕ}
    (hsched : m * (rr (i + 1) + d) ≤ rr i)
    (hlift : DecimLift nn V m dec)
    (hCA : CorrelatedAgreementCurveUDParam F (nn (i + 1)) (V (i + 1)) (rr (i + 1) + d) m)
    (hfar : ¬ closeN (V i) (rr i) w) :
    (towerGood nn V (fun j => rr j + d) m dec i w).card ≤ (m - 1) * (rr (i + 1) + d + 1) := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨g, hg, hagree⟩ := hCA (dec i w) (towerGood nn V (fun j => rr j + d) m dec i w)
    (fun α hα => mem_towerGood.1 hα) hcon
  exact hfar (closeN_mono hsched (hlift i w g hg (rr (i + 1) + d) hagree))

/-- **⚑ THE SLACKENED STEP THE CHAIN CONSUMES** — the ladder form of
`FriFoldConsistencyDichotomy.chainStepSlack_of_gap`. If the prover's committed word is within `d`
of the prescribed fold, and the fold is `(rᵢ₊₁ + d)`-far, then the COMMITTED word is still
`rᵢ₊₁`-far: the Hamming triangle spends exactly the margin. This is why `d > 0` is worth having —
at `d = 0` the gate is an EQUALITY and the spot check pays nothing
(`FriFoldConsistencyDichotomy.exact_gate_pays_nothing`). -/
theorem chainStepSlackLadder {i : ℕ} {w : Fin (nn i) → F} {w' : Fin (nn (i + 1)) → F} {ρ : F}
    {d : ℕ}
    (hρ : ρ ∉ towerGood nn V (fun j => rr j + d) m dec i w)
    (hd : hammingDist w' (towerFold nn m dec i w ρ) ≤ d) :
    ¬ closeN (V (i + 1)) (rr (i + 1)) w' := by
  rintro ⟨g, hg, hgc⟩
  refine hρ (mem_towerGood.mpr ⟨g, hg, ?_⟩)
  calc hammingDist (towerFold nn m dec i w ρ) g
      ≤ hammingDist (towerFold nn m dec i w ρ) w' + hammingDist w' g :=
        hammingDist_triangle _ _ _
    _ ≤ d + rr (i + 1) := Nat.add_le_add (by rwa [hammingDist_comm]) hgc
    _ = rr (i + 1) + d := Nat.add_comm _ _

end Ladder

/-! ## §4 — ⚑ THE COMPOSED BOUND, with the radius allowed to FALL across the round. -/

section Compose

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Nonempty F]
variable {D : Type} [Fintype D] [DecidableEq D]

/-- `FriSoundness.disagree` and Mathlib's `hammingDist` count the same set. -/
theorem disagree_card_eq_hammingDist {ι : Type} [Fintype ι] [DecidableEq ι] (f g : ι → F) :
    (disagree f g).card = hammingDist f g := rfl

/-- The one-query oracle computation: ask the FS point, halt. -/
def probe (p : D) : OracleComp D F Unit := OracleComp.query p (fun _ => OracleComp.pure ())

theorem probe_bounded (p : D) : QueryBounded 1 (probe (F := F) p) :=
  QueryBounded.query 0 p _ (fun _ => QueryBounded.pure 0 ())

theorem hitWin_probe (E : D → Finset F) (p : D) (H : D → F) :
    hitWin E (probe (F := F) p) H = decide (H p ∈ E p) := by
  simp [probe, hitWin_query, hitWin_pure]

/-- **The FS branch, priced by the landed ROM counting.** The random oracle's answer at a FIXED
point lands in a bad set of size `≤ b` with probability `≤ b/|F|` — `hit_bound` at a one-query
computation, so the FS addend here is the same object `chain_far_survival_slack` spends. -/
theorem fs_point_bound (p : D) (E : Finset F) {b : ℕ} (hE : E.card ≤ b) :
    winProb (fun H : D → F => decide (H p ∈ E)) ≤ (b : ℝ) / (Fintype.card F : ℝ) := by
  classical
  have hcap : ∀ q : D, ((fun q : D => if q = p then E else (∅ : Finset F)) q).card ≤ b := by
    intro q
    by_cases h : q = p
    · simpa [h] using hE
    · simp [h]
  have h := hit_bound (probe (F := F) p) (probe_bounded p)
    (fun q : D => if q = p then E else (∅ : Finset F)) hcap
  have hfun : hitWin (fun q : D => if q = p then E else (∅ : Finset F)) (probe (F := F) p)
      = fun H : D → F => decide (H p ∈ E) := by
    funext H
    rw [hitWin_probe]
    simp
  rw [hfun] at h
  simpa using h

open Classical in
/-- **⚑⚑ THE COMPOSED BOUND, ONE ROUND, RADIUS FALLING.** For an ARBITRARY round-1 commitment
`S : F → (Fin n₁ → F)` — adaptive on the FS challenge, with NO fold-consistency gate anywhere in
the statement — the probability, over the random oracle AND the query sample jointly, that

  * farness DIES at round 1 (`S`'s commitment is `r₁`-CLOSE to the layer-1 code), and
  * the verifier's `k`-point fold-consistency spot check PASSES,

is at most `b/|F| + (1−δ)^k`, for any `δ` with `δ·n₁ ≤ d`, where `b` caps the
`(r₁+d)`-good challenge set of `w0`.

This is `FriFoldConsistencyDichotomy.strategy_soundness_compose` with ONE change, and it is the
change §1 proves is forced: the surviving radius at round 1 is `r₁`, NOT the round-0 radius. The
proof is the same two-branch split — `winProb_le_add` unions "the challenge was good" with "the
prover deviated by more than `d` and the spot check still passed", `winProb_fst` lifts the FS
bound off the query coordinate, `winProb_le_of_fiber` + `accept_prob_le` price the query fibre,
and the Hamming triangle is what makes the two branches cover the event. -/
theorem compose_one_round
    {n₀ n₁ : ℕ} (V₁ : Set (Fin n₁ → F))
    (fold : (Fin n₀ → F) → F → (Fin n₁ → F))
    (w0 : Fin n₀ → F) (p : D)
    (good : Finset F) {b : ℕ} (hb : good.card ≤ b)
    {r₁ d k : ℕ} {δ : ℝ}
    (hgood : ∀ ρ : F, ρ ∉ good → ¬ closeN V₁ (r₁ + d) (fold w0 ρ))
    (S : F → (Fin n₁ → F))
    (hn₁ : 0 < n₁) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hδd : δ * (n₁ : ℝ) ≤ (d : ℝ)) :
    winProb (fun ω : (D → F) × (Fin k → Fin n₁) =>
        decide (closeN V₁ r₁ (S (ω.1 p)))
          && decide (Accepts (S (ω.1 p)) (fold w0 (ω.1 p)) ω.2))
      ≤ (b : ℝ) / (Fintype.card F : ℝ) + (1 - δ) ^ k := by
  classical
  have hcard : Fintype.card (Fin n₁) = n₁ := Fintype.card_fin n₁
  have hιpos : 0 < Fintype.card (Fin n₁) := by rw [hcard]; exact hn₁
  have hQne : Nonempty (Fin k → Fin n₁) := ⟨fun _ => ⟨0, hn₁⟩⟩
  refine le_trans (winProb_le_add
      (f := fun ω : (D → F) × (Fin k → Fin n₁) =>
        decide (closeN V₁ r₁ (S (ω.1 p)))
          && decide (Accepts (S (ω.1 p)) (fold w0 (ω.1 p)) ω.2))
      (g := fun ω : (D → F) × (Fin k → Fin n₁) => decide (ω.1 p ∈ good))
      (h := fun ω : (D → F) × (Fin k → Fin n₁) =>
        (!decide (hammingDist (S (ω.1 p)) (fold w0 (ω.1 p)) ≤ d))
          && decide (Accepts (S (ω.1 p)) (fold w0 (ω.1 p)) ω.2)) ?_) ?_
  · intro ω hω
    rw [Bool.and_eq_true] at hω
    obtain ⟨hω1, hω2⟩ := hω
    by_cases hc : hammingDist (S (ω.1 p)) (fold w0 (ω.1 p)) ≤ d
    · refine Or.inl (decide_eq_true ?_)
      by_contra hmem
      refine hgood (ω.1 p) hmem ?_
      obtain ⟨g, hg, hgc⟩ := of_decide_eq_true hω1
      refine ⟨g, hg, ?_⟩
      calc hammingDist (fold w0 (ω.1 p)) g
          ≤ hammingDist (fold w0 (ω.1 p)) (S (ω.1 p)) + hammingDist (S (ω.1 p)) g :=
            hammingDist_triangle _ _ _
        _ ≤ d + r₁ := Nat.add_le_add (by rwa [hammingDist_comm]) hgc
        _ = r₁ + d := Nat.add_comm _ _
    · exact Or.inr (by simp [hc, hω2])
  refine add_le_add ?_ ?_
  · rw [winProb_fst (Ω₂ := Fin k → Fin n₁) (fun H : D → F => decide (H p ∈ good))]
    exact fs_point_bound p good hb
  · have hβ : (0 : ℝ) ≤ (1 - δ) ^ k := pow_nonneg (by linarith) k
    refine winProb_le_of_fiber hβ _ ?_
    intro H
    show ((Finset.univ.filter (fun Q : Fin k → Fin n₁ =>
        ((!decide (hammingDist (S (H p)) (fold w0 (H p)) ≤ d))
          && decide (Accepts (S (H p)) (fold w0 (H p)) Q)) = true)).card : ℝ)
      ≤ (1 - δ) ^ k * (Fintype.card (Fin k → Fin n₁) : ℝ)
    have hcardQ : (Fintype.card (Fin k → Fin n₁) : ℝ) = (Fintype.card (Fin n₁) : ℝ) ^ k := by
      rw [Fintype.card_fun]
      push_cast
      simp
    have hpos : (0 : ℝ) < (Fintype.card (Fin n₁) : ℝ) ^ k := by
      have hc : (0 : ℝ) < (Fintype.card (Fin n₁) : ℝ) := by exact_mod_cast hιpos
      positivity
    rw [hcardQ]
    by_cases hc : hammingDist (S (H p)) (fold w0 (H p)) ≤ d
    · have hz : (Finset.univ.filter (fun Q : Fin k → Fin n₁ =>
          ((!decide (hammingDist (S (H p)) (fold w0 (H p)) ≤ d))
            && decide (Accepts (S (H p)) (fold w0 (H p)) Q)) = true)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro Q _
        simp [hc]
      rw [hz, Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg hβ (le_of_lt hpos)
    · have hgt : δ * (Fintype.card (Fin n₁) : ℝ)
          < ((disagree (S (H p)) (fold w0 (H p))).card : ℝ) := by
        rw [disagree_card_eq_hammingDist, hcard]
        have hlt : d < hammingDist (S (H p)) (fold w0 (H p)) := Nat.lt_of_not_le hc
        have hd' : (d : ℝ) < (hammingDist (S (H p)) (fold w0 (H p)) : ℝ) := by exact_mod_cast hlt
        linarith
      have hmass := accept_prob_le (f := S (H p)) (g := fold w0 (H p)) k hιpos hδ0 hgt
      have hsub : (Finset.univ.filter (fun Q : Fin k → Fin n₁ =>
          ((!decide (hammingDist (S (H p)) (fold w0 (H p)) ≤ d))
            && decide (Accepts (S (H p)) (fold w0 (H p)) Q)) = true))
          ⊆ (Finset.univ.filter (fun Q : Fin k → Fin n₁ =>
              Accepts (S (H p)) (fold w0 (H p)) Q)) := by
        intro Q hQ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true] at hQ ⊢
        exact of_decide_eq_true hQ.2
      have hcc : ((Finset.univ.filter (fun Q : Fin k → Fin n₁ =>
          ((!decide (hammingDist (S (H p)) (fold w0 (H p)) ≤ d))
            && decide (Accepts (S (H p)) (fold w0 (H p)) Q)) = true)).card : ℝ)
          ≤ ((Finset.univ.filter (fun Q : Fin k → Fin n₁ =>
              Accepts (S (H p)) (fold w0 (H p)) Q)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      exact hcc.trans ((div_le_iff₀ hpos).mp hmass)

end Compose

/-! ## §5 — ⚑ THE FIRE at the deployed `2^19` tower, and the five-layer margin ladder. -/

section Deployed

/-- **`towerRR` HAS NO ROOM.** The landed geometric schedule `towerRR i = 8^(5−i)` satisfies the
fold law with EQUALITY at every rung, so it admits no margin at all: `8·(towerRR 1 + 1) = 32776 >
32768 = towerRR 0`. That is why §2 needed a new schedule rather than a reuse. -/
theorem towerRR_has_no_margin : ¬ (8 * (towerRR 1 + 1) ≤ towerRR 0) := by
  norm_num [towerRR]

/-- **⚑ THE MARGIN CAP AT ALL FIVE WELDED LAYERS.** At every layer of the deployed `2^19` tower,
a word that is `mRRᵢ`-far has at most `7·(mRRᵢ₊₁ + 2)` challenges folding it within
`mRRᵢ₊₁ + 1` of the next layer's code. So the POSITIVE-radius schedule with a POSITIVE margin
runs the whole tower — this is the schedule `FriSetupTower.lean:49-54` names as its next rung. -/
theorem tower_margin_cap : ∀ (i : ℕ), i < 5 → ∀ w : Fin (twSz i) → BabyBear,
    ¬ closeN (towerV i) (mRR i) w →
      (towerGood twSz towerV (fun j => mRR j + 1) 8 towerDec i w).card
        ≤ 7 * (mRR (i + 1) + 2) := by
  intro i hi w hfar
  exact goodMargin_card_le (mRR_margin i hi) decimLift_of_tower (hCA_margin i hi) hfar

/-- **⚑ THE SLACKENED STEP AT ALL FIVE WELDED LAYERS.** A prover whose committed layer-`(i+1)`
word is within `1` of the prescribed fold, at a challenge outside the margin good set, is STILL
`mRRᵢ₊₁`-far. This is `ChainStepSlack` at the deployed tower at a POSITIVE radius with a
POSITIVE slack — the object `FriFoldConsistencyDichotomy.chain_far_slack_of_farCover` consumes,
which at `d = 0` degenerates to the exact gate that pays nothing. -/
theorem tower_margin_slack (i : ℕ) (w : Fin (twSz i) → BabyBear)
    (w' : Fin (twSz (i + 1)) → BabyBear) (ρ : BabyBear)
    (hρ : ρ ∉ towerGood twSz towerV (fun j => mRR j + 1) 8 towerDec i w)
    (hd : hammingDist w' (towerFold twSz 8 towerDec i w ρ) ≤ 1) :
    ¬ closeN (towerV (i + 1)) (mRR (i + 1)) w' :=
  chainStepSlackLadder hρ hd

/-- The deployed layer-0 → layer-1 arity-8 fold. `DecimLiftDischarge.towerFold_is_Fold` proves
this IS `FriFoldArity.Fold` at `towerS 0`'s geometry — the real deployed fold, not a stand-in. -/
noncomputable def dfold : (Fin (twSz 0) → BabyBear) → BabyBear → (Fin (twSz 1) → BabyBear) :=
  towerFold twSz 8 towerDec 0

/-- The composition's good set: the challenges folding `farWord` within `6371 = r₁ + d` of the
layer-1 code. By-definition — the CONTENT is `dgood_card_le`. -/
noncomputable def dgood : Finset BabyBear := towerGood twSz towerV cRR 8 towerDec 0 farWord

/-- **⚑ THE CAP — `(8−1)·(6371+1) = 44604`** — from the landed per-layer correlated agreement
(`hCA_compose`), the landed decimation-lift weld (`decimLift_of_tower`), the tight fold law
(`cRR_sched`) and the INHABITED layer-0 farness (`farWord_far_compose`). No new hypothesis. -/
theorem dgood_card_le : dgood.card ≤ 44604 := by
  have h := towerGood_card_le (nn := twSz) (V := towerV) (rr := cRR) (m := 8) (dec := towerDec)
    (i := 0) (w := farWord) cRR_sched decimLift_of_tower hCA_compose farWord_far_compose
  simpa [dgood, cRR] using h

/-- Outside the good set the fold is `(r₁ + d) = 2275 + 4096 = 6371`-FAR from the layer-1 code. -/
theorem dgood_far (ρ : BabyBear) (hρ : ρ ∉ dgood) :
    ¬ closeN (towerV 1) (2275 + 4096) (dfold farWord ρ) := by
  intro hclose
  refine hρ ?_
  rw [dgood, mem_towerGood]
  exact hclose

open Classical in
/-- **⚑⚑ THE COMPOSED BOUND FIRES AT THE DEPLOYED `2^19` TOWER, BOTH ADDENDS MEANINGFUL.** From
the PROVEN-far `farWord` at the real `2^19` top domain (`50968`-far — a positive radius, and
INHABITED, which is exactly what fails at the `|ι| = 16` toy), one round of the deployed arity-8
fold into the `2^16` layer-1 domain, against an ARBITRARY adaptive round-1 commitment `S`:

    Pr[ farness dies at radius 1  ∧  the 38-query fold check passes ]
      ≤ 44604/|BabyBear|  +  (15/16)^38.

The FS addend is the CA-capped bad-challenge mass; the query addend is a genuine sub-`1`
spot-check mass at `δ = 1/16` (admissible because `δ·2^16 = 4096 ≤ 6370 = d`). -/
theorem deployed_compose (p : towerD 5 twSz BabyBear)
    (S : BabyBear → (Fin (twSz 1) → BabyBear)) :
    winProb (fun ω : (towerD 5 twSz BabyBear → BabyBear) × (Fin 38 → Fin (twSz 1)) =>
        decide (closeN (towerV 1) 2275 (S (ω.1 p)))
          && decide (Accepts (S (ω.1 p)) (dfold farWord (ω.1 p)) ω.2))
      ≤ (44604 : ℝ) / (Fintype.card BabyBear : ℝ) + (1 - (1 / 16 : ℝ)) ^ 38 :=
  compose_one_round (V₁ := towerV 1) (fold := dfold) (w0 := farWord) p dgood dgood_card_le
    (r₁ := 2275) (d := 4096) (k := 38) (δ := (1 / 16 : ℝ)) dgood_far S
    (by norm_num [twSz]) (by norm_num) (by norm_num) (by norm_num [twSz])

/-- **⚑ THE COMPOSED BOUND IS GENUINELY SUB-`1`** — `≈ 0.0861`, not a restated `≤ 1`. Contrast
`FriFoldConsistencyDichotomy.exact_gate_pays_nothing`: at `d = 0` the query addend is `≥ 1` and
the whole composition is vacuous. -/
theorem deployed_compose_lt_one :
    (44604 : ℝ) / (Fintype.card BabyBear : ℝ) + (1 - (1 / 16 : ℝ)) ^ 38 < 1 := by
  rw [ZMod.card]
  norm_num

/-- The constant word is a layer-1 codeword (the degree-`0` monomial scaled). -/
theorem const_mem_towerV1 (c : BabyBear) : (fun _ : Fin (twSz 1) => c) ∈ towerV 1 := by
  have h1 : monoW (twSz 1) 0 (wchain 2)
      ∈ Dregg2.Circuit.FriSetupTower.rsCode (twSz 1) (2 ^ 13) (wchain 2) :=
    Dregg2.Circuit.FriSetupTower.monoW_mem (wchain 2) (by norm_num)
  have h2 : c • monoW (twSz 1) 0 (wchain 2)
      ∈ Dregg2.Circuit.FriSetupTower.rsCode (twSz 1) (2 ^ 13) (wchain 2) :=
    Submodule.smul_mem _ c h1
  have h3 : c • monoW (twSz 1) 0 (wchain 2) = (fun _ : Fin (twSz 1) => c) := by
    funext x
    simp [Dregg2.Circuit.FriSetupTower.monoW]
  rw [h3] at h2
  exact h2

open Classical in
/-- **⚑ THE COMPOSED EVENT IS REACHABLE at the deployed instance** — the `44604/|BabyBear| +
(15/16)^38` bound is over a NON-EMPTY event, not over nothing. Witness: the prover that commits
the CONSTANT word matching the fold at the queried point (a genuine layer-1 codeword, so farness
dies with certainty) against a query sample that only ever lands there. Exactly the polarity
`FriQuerySoundness.far_accepted_by_missing_query` records: soundness here is genuinely
probabilistic. -/
theorem deployed_compose_event_nonempty (p : towerD 5 twSz BabyBear) :
    ∃ (S : BabyBear → (Fin (twSz 1) → BabyBear))
      (ω : (towerD 5 twSz BabyBear → BabyBear) × (Fin 38 → Fin (twSz 1))),
      (decide (closeN (towerV 1) 2275 (S (ω.1 p)))
        && decide (Accepts (S (ω.1 p)) (dfold farWord (ω.1 p)) ω.2)) = true := by
  classical
  have hy : (0 : ℕ) < twSz 1 := by norm_num [twSz]
  refine ⟨fun ρ => fun _ => dfold farWord ρ ⟨0, hy⟩,
    (fun _ => 0, fun _ => ⟨0, hy⟩), ?_⟩
  have hclose : closeN (towerV 1) 2275 (fun _ : Fin (twSz 1) => dfold farWord 0 ⟨0, hy⟩) :=
    ⟨(fun _ : Fin (twSz 1) => dfold farWord 0 ⟨0, hy⟩), const_mem_towerV1 _,
      by rw [hammingDist_self]; omega⟩
  have hacc : Accepts (fun _ : Fin (twSz 1) => dfold farWord 0 ⟨0, hy⟩)
      (dfold farWord 0) (fun _ : Fin 38 => (⟨0, hy⟩ : Fin (twSz 1))) := fun _ => rfl
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hclose, hacc⟩

/-- BOTH addends are real: the query addend is a strictly positive, strictly sub-`1` mass. -/
theorem deployed_query_addend_nondegenerate :
    (0 : ℝ) < (1 - (1 / 16 : ℝ)) ^ 38 ∧ (1 - (1 / 16 : ℝ)) ^ 38 < 1 := by
  constructor <;> norm_num

/-- …and the FS addend is a strictly positive, strictly sub-`1` mass. -/
theorem deployed_fs_addend_nondegenerate :
    (0 : ℝ) < (44604 : ℝ) / (Fintype.card BabyBear : ℝ) ∧
      (44604 : ℝ) / (Fintype.card BabyBear : ℝ) < 1 := by
  rw [ZMod.card]
  constructor <;> norm_num

end Deployed

/-! ## Kernel-clean keystones. -/

#assert_all_clean [
  chainStepGap_free,
  constant_radius_margin_infeasible,
  closeN_of_card_le,
  n2_margin_forces_huge_top,
  n2_forces_huge_top,
  deployed_n2_positive_radius_impossible,
  deployed_n2_positive_margin_impossible,
  mRR_margin,
  mRR_sched,
  hCA_margin,
  farWord_far_margin,
  cRR_sched,
  hCA_compose,
  farWord_far_compose,
  chainStepGapLadder_holds,
  goodMargin_card_le,
  chainStepSlackLadder,
  disagree_card_eq_hammingDist,
  probe_bounded,
  hitWin_probe,
  fs_point_bound,
  compose_one_round,
  towerRR_has_no_margin,
  tower_margin_cap,
  tower_margin_slack,
  dgood_card_le,
  dgood_far,
  deployed_compose,
  deployed_compose_lt_one,
  deployed_query_addend_nondegenerate,
  deployed_fs_addend_nondegenerate,
  const_mem_towerV1,
  deployed_compose_event_nonempty
]

end Dregg2.Circuit.FriPositiveRadiusSchedule

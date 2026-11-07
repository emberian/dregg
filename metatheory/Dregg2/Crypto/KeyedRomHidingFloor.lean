/-
# `Dregg2.Crypto.KeyedRomHidingFloor` — the KEYED-ROM HIDING FLOOR, **PROVED**, by the same
lazy-sampling counting that already proves the birthday collision bound.

## What this file answers

Commitment HIDING in this tree had the same disease collision-resistance had before
`RomQueryFloor`: the only stated floor lived at a class with no content.
`Metatheory.Open.BlindedSpanHiding` (Lane B) reduces a span-recovery hiding break of the deployed
wide blinded commitment to `WidePreimageFloor` — and then PROVES, in the same file, that the
`CostAdversary.IsPolyTime` instance of that floor is FALSE at deployed parameters
(`widePreimageFloor_polyTime_false`): `idAdv` prices answer SIZE, never search difficulty, so the
constant finder that hardcodes the fixed honest opening is `IsPolyTime` and wins with probability
`1`. Every hiding statement conditioned on that floor is therefore VACUOUS at the deployed hash.

The repo's PROVEN fix for the collision side is the QUERY-BOUNDED KEYED RANDOM ORACLE:
`RomQueryFloor.birthday_bound` ((Q² + 1)/|R|, information-theoretic, no assumption) at the class
`RomEff`/`KeyedRomEff`, where the oracle is sampled AFTER the adversary tree is fixed — which is
what defeats hardcoding. This file transports that discipline to HIDING. The argument is the same
one-sentence fact that carries the birthday bound (`RomCounting.condProb_fresh_eq`): *what the
adversary has not queried, it does not know.*

## The game (§2) — two-world indistinguishability, `FloorGames.distAdv`-shaped

The adversary FIXES two messages `msg0 msg1 : Msg` (equal length BY TYPE — one abstract type of
fixed-width span digests, so "equal-length" is enforced by the formalization, not checked) and a
challenge-indexed query tree, all BEFORE anything is sampled. The challenger samples the oracle
`H : Msg × B → R` uniformly and the blinding `r : B` uniformly, and hands the adversary the
challenge digest `H (m_b, r)` — the deployed `hash(span_digest ‖ BLINDING)` shape with the
blinding a HIDDEN coordinate of the preimage. The adversary makes up to `Q` oracle queries and
outputs a guess bit; `hidingAdv` is the DIFFERENCE of the two worlds' accept probabilities —
a genuine distinguishing advantage (`FloorGames` §7's `distAdv` shape, NOT a `winProb`), which is
exactly the "full two-world indistinguishability" `BlindedSpanHiding` §(c).1 names as open.

## The bound (§4), PROVED, information-theoretic:  `hidingAdv ≤ 2·Q / |B|`

(`|B|` = the BLINDING space — the prompt's "R"; also stated in the cruder `(2Q + 1)/|B|` form.)
Identical-until-bad, done as finite counting with NO measure theory and NO assumption:

  * **The reprogramming lemma** (`condProb_pin_untouched`, §1): pinning the oracle at a point `d`
    does not move the probability of any event that is a function of the tree's output GATED ON
    "`d` was not queried". Proof: the update-at-`d` bijection between slices preserves `eval` and
    `queried` on that event (`RomOracle.OracleComp.eval_congr_of_agree_on_queried`), so all
    `|R|` slices of `RomCounting.condProb_split` carry equal weight.
  * **Identical-until-bad** (`condProb_pin_diff_le`): real world (challenge = `H (m_b, r)`,
    i.e. the oracle PINNED at the challenge point) and hybrid world (challenge a fresh uniform
    value, oracle free) differ by at most the probability of the BAD event — the adversary
    queries the challenge point `(m_b, r)`.
  * **The union bound** (`sum_touch_le`): a `Q`-query tree queries at most `Q` points per run, so
    summed over the uniform hidden blinding `r` the bad event has mass at most `Q/|B|`
    (`RomOracle.QueryBounded.queried_length_le`). In the hybrid the view is `b`-independent, so
    the advantage collapses through two hybrid hops: `2·Q/|B|`.

Same status as `birthday_bound`: a counting fact about the finite function space `Msg × B → R`,
with the query budget the only resource.

## Non-vacuity — BOTH poles, PROVED (§5, §6)

  * **`⊤` is not hiding**: the unrestricted adversary — a function reading the WHOLE experiment
    tape `(H, r)`, which is exactly what the raw `accept` type permits and the query-bounded class
    forbids — recomputes `H (m₀, r)` and compares it to the challenge: advantage EXACTLY
    `1 − 1/|R|` (`topAdv_hidingAdv`). At the deployed shape that is ≥ 1/2 at every parameter, so
    the unrestricted hiding floor is FALSE (`hidingTop_false`) and this file's floor is not
    vacuously true. The CANARY (`canary_top_breaks_bound`) pins a concrete instance where
    `topAdv`'s advantage `3/4` violates the `Q = 1` bound `1/4` — hence `topAdv` is PROVABLY not
    in the one-query class (`canary_topAdv_not_oneQuery`).
  * **The class is inhabited by a REAL winner**: the one-query distinguisher that probes
    `(msg0, r₀)` at a fixed blinding guess `r₀` has advantage EXACTLY `(1 − 1/|R|)/|B| > 0`
    (`oneQueryAdv_hidingAdv`, `oneQueryAdv_hidingAdv_pos`) — it really queries, really wins
    sometimes, and sits inside the bound. And the hardcoding adversary is DEFANGED, not excluded:
    a `0`-query guesser is admitted and its advantage is EXACTLY `0`
    (`zeroQuery_hidingAdv_eq_zero`) — sampling the blinding after the adversary is fixed is what
    kills it, the `KeyedRomFloor.fixedPairAdv_negl` story on the hiding side.

## The re-grounding (§7)

`spanHiding_regrounded`: at the deployed-shape family (`λ`-bit blinding felt, wide digest), the
keyed query-bounded hiding floor HOLDS — every `Q(λ)`-query adversary's span-distinguishing
advantage is `≤ (2·Q(λ) + 1)/2^λ`, negligible for polynomial `Q` — while Lane B's
`WidePreimageFloor (IsPolyTime …)`, the floor the old conditional hiding statement rested on, is
REFUTED (re-exported from `BlindedSpanHiding`, read-only). The proved keyed floor is the
replacement: same deployed object, a class with content, no hypothesis.

## HONEST HEADER — what is and is not claimed

This is **ROM hiding**: it models the wide Poseidon2 as a keyed random oracle, and the bound is
INFORMATION-THEORETIC in the query-bounded class — no computational assumption, the same status as
the birthday collision bound already in the tree (`RomQueryFloor` §5). The ONE named residual is
the ROM-modeling of Poseidon2 itself (standard, named, NOT discharged here — exactly the residual
`RomQueryFloor`'s collision floor carries). We do NOT claim hiding against arbitrary
polynomial-time adversaries: the class is the query-bounded keyed class, whose budget is a QUERY
count (unbounded work between queries is allowed, `RomQueryFloor`'s "named residual" section), and
the `⊤`-pole theorem shows the unrestricted claim would be FALSE. "Equal-length messages" is
enforced by TYPE (one fixed-width message type), not by a length check.

## Axiom hygiene

`#assert_all_clean` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`, no fresh `axiom`, no
`native_decide`. NEW ADDITIVE file; imports read-only.
-/
import Dregg2.Crypto.KeyedRomFloor
import Metatheory.Open.BlindedSpanHiding
import Dregg2.Tactics
import Mathlib.Tactic

namespace Dregg2.Crypto.KeyedRomHidingFloor

open Dregg2.Crypto.ConcreteSecurity
  (Ensemble Negl PolyBounded negl_two_pow negl_mul_poly negl_of_eventually_le not_negl_one)
open Dregg2.Crypto.ProbCrypto (winProb winProb_nonneg winProb_le_one winProb_top)
open Dregg2.Crypto.RomCounting
  (cyl mem_cyl cyl_empty cyl_nonempty cyl_card_pos condProb condProb_nonneg condProb_le_one
   condProb_congr condProb_le_of_imp condProb_eq_zero condProb_eq_one condProb_cyl_empty
   condProb_split condProb_fresh_eq cyl_insert_card_eq)
open Dregg2.Crypto.RomQueryFloor (condProb_two_fresh_eq)
open Dregg2.Crypto.RomOracle (OracleComp QueryBounded)

set_option autoImplicit false
-- As in `RomCounting`: the abstract-oracle lemmas carry the section's instances uniformly so every
-- lemma applies at the product domain without instance juggling at the call site.
set_option linter.unusedSectionVars false

/-! ## §1 — the general reprogramming machinery, over an arbitrary oracle `D → R`.

`RomCounting` proves lazy sampling for the FRESH-point event (`condProb_fresh_eq`) — the collision
bound's engine. Hiding needs one more general fact, NOT in the tree yet: pinning the oracle at a
point the adversary does not query moves NOTHING. That is the identical-until-bad hop, and this
section proves it by the same slice bijection `cyl_insert_card_eq` uses, upgraded to carry the
tree's output along (`OracleComp.eval_congr_of_agree_on_queried` is what makes the upgrade true). -/

section Reprogram

variable {D R : Type} [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R]

/-- **`condProb` SPLITS OVER A BOOLEAN GATE.** The win event decomposes into its gated halves —
finite additivity, as filter-count arithmetic. The decomposition step of identical-until-bad. -/
theorem condProb_gate_split (C : Finset (D → R)) (w g : (D → R) → Bool) :
    condProb C w
      = condProb C (fun H => w H && g H) + condProb C (fun H => w H && !g H) := by
  unfold condProb
  rw [← add_div]
  congr 1
  have h1 : C.filter (fun H => (w H && g H) = true)
      = (C.filter (fun H => w H = true)).filter (fun H => g H = true) := by
    rw [Finset.filter_filter]
    exact Finset.filter_congr (fun H _ => by simp [Bool.and_eq_true])
  have h2 : C.filter (fun H => (w H && !g H) = true)
      = (C.filter (fun H => w H = true)).filter (fun H => ¬ (g H = true)) := by
    rw [Finset.filter_filter]
    exact Finset.filter_congr (fun H _ => by simp [Bool.and_eq_true])
  rw [h1, h2]
  exact_mod_cast (Finset.card_filter_add_card_filter_not
    (s := C.filter (fun H => w H = true)) (fun H => g H = true)).symm

/-- **THE SLICE BIJECTION CARRIES THE TREE'S OUTPUT.** On the event "`d` was NOT queried", the
update-at-`d` bijection between the `c₁`-slice and the `c₂`-slice preserves the tree's output and
its query list (`eval_congr_of_agree_on_queried`), so the two slices give the event EQUAL counts.
This is the counting heart of the reprogramming lemma. -/
theorem untouched_filter_card_eq {A : Type} (M : OracleComp D R A) (φ : A → Bool)
    (d : D) (S : Finset D) (σ : D → R) (c₁ c₂ : R) (hd : d ∉ S) :
    ((cyl (insert d S) (Function.update σ d c₁)).filter
        (fun H => (φ (M.eval H) && !decide (d ∈ M.queried H)) = true)).card
      = ((cyl (insert d S) (Function.update σ d c₂)).filter
        (fun H => (φ (M.eval H) && !decide (d ∈ M.queried H)) = true)).card := by
  have key : ∀ (a b : R) (H : D → R),
      H ∈ (cyl (insert d S) (Function.update σ d a)).filter
        (fun H => (φ (M.eval H) && !decide (d ∈ M.queried H)) = true) →
      Function.update H d b ∈ (cyl (insert d S) (Function.update σ d b)).filter
        (fun H => (φ (M.eval H) && !decide (d ∈ M.queried H)) = true) := by
    intro a b H hH
    rw [Finset.mem_filter] at hH ⊢
    obtain ⟨hcyl, hpred⟩ := hH
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hpred
    obtain ⟨hφ, hnq⟩ := hpred
    have hag : ∀ x ∈ M.queried H, H x = Function.update H d b x := by
      intro x hx
      have hxd : x ≠ d := fun h => hnq (h ▸ hx)
      rw [Function.update_of_ne hxd]
    obtain ⟨hev, hq⟩ := M.eval_congr_of_agree_on_queried H (Function.update H d b) hag
    refine ⟨?_, ?_⟩
    · rw [mem_cyl] at hcyl ⊢
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hxS
      · simp
      · have hxd : x ≠ d := by rintro rfl; exact hd hxS
        rw [Function.update_of_ne hxd, Function.update_of_ne hxd]
        have := hcyl x (Finset.mem_insert_of_mem hxS)
        rwa [Function.update_of_ne hxd] at this
    · simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
      exact ⟨hev ▸ hφ, hq ▸ hnq⟩
  have pin : ∀ (a : R) (H : D → R),
      H ∈ (cyl (insert d S) (Function.update σ d a)).filter
        (fun H => (φ (M.eval H) && !decide (d ∈ M.queried H)) = true) → H d = a := by
    intro a H hH
    have := (mem_cyl.1 (Finset.mem_filter.1 hH).1) d (Finset.mem_insert_self d S)
    simpa using this
  refine Finset.card_bij' (fun H _ => Function.update H d c₂) (fun K _ => Function.update K d c₁)
    (fun H hH => key c₁ c₂ H hH) (fun K hK => key c₂ c₁ K hK) (fun H hH => ?_) (fun K hK => ?_)
  · show Function.update (Function.update H d c₂) d c₁ = H
    rw [Function.update_idem, ← pin c₁ H hH, Function.update_eq_self]
  · show Function.update (Function.update K d c₁) d c₂ = K
    rw [Function.update_idem, ← pin c₂ K hK, Function.update_eq_self]

/-- **⚑ THE REPROGRAMMING LEMMA — pinning an UNQUERIED point moves nothing.** For any event that
is a function of the tree's output GATED ON "`d` was not queried", the conditional probability in
the world where the oracle is pinned at `d` equals the free-world probability. This is the general
lazy-sampling fact hiding needs beyond `condProb_fresh_eq`: the challenge value can be pinned (to
the challenge the adversary was handed) without disturbing anything the adversary can see short of
querying the challenge point itself. -/
theorem condProb_pin_untouched {A : Type} (M : OracleComp D R A) (φ : A → Bool)
    (d : D) (S : Finset D) (σ : D → R) (c : R) (hd : d ∉ S) :
    condProb (cyl (insert d S) (Function.update σ d c))
        (fun H => φ (M.eval H) && !decide (d ∈ M.queried H))
      = condProb (cyl S σ) (fun H => φ (M.eval H) && !decide (d ∈ M.queried H)) := by
  have hRpos : (0 : ℝ) < (Fintype.card R : ℝ) := by
    have : Nonempty R := ⟨σ d⟩
    exact_mod_cast Fintype.card_pos
  rw [condProb_split S σ d hd]
  have hval : ∀ c' : R,
      condProb (cyl (insert d S) (Function.update σ d c'))
          (fun H => φ (M.eval H) && !decide (d ∈ M.queried H))
        = condProb (cyl (insert d S) (Function.update σ d c))
          (fun H => φ (M.eval H) && !decide (d ∈ M.queried H)) := by
    intro c'
    unfold condProb
    rw [untouched_filter_card_eq M φ d S σ c' c hd, cyl_insert_card_eq S σ d c' c hd]
  rw [Finset.sum_congr rfl (fun c' _ => hval c'), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  field_simp

/-- **⚑ IDENTICAL-UNTIL-BAD.** The pinned world (oracle forced to `c` at `d` — the REAL world,
where the challenge is the oracle's value at the challenge point) and the free world (the HYBRID,
where the challenge is fresh and independent) assign the tree's acceptance probabilities that
differ by AT MOST the free-world probability of the bad event — the tree queries `d`.

Discharged by `condProb_pin_untouched` twice: once at `φ := id` (the good halves agree) and once
at `φ := const true` (the bad events have equal mass in both worlds). -/
theorem condProb_pin_diff_le (M : OracleComp D R Bool) (d : D) (σ : D → R) (c : R) :
    |condProb (cyl (insert d (∅ : Finset D)) (Function.update σ d c)) (fun H => M.eval H)
        - condProb (cyl (∅ : Finset D) σ) (fun H => M.eval H)|
      ≤ condProb (cyl (∅ : Finset D) σ) (fun H => decide (d ∈ M.queried H)) := by
  have hd : d ∉ (∅ : Finset D) := by simp
  -- Split both worlds over the bad gate.
  have hsplitP := condProb_gate_split (cyl (insert d (∅ : Finset D)) (Function.update σ d c))
    (fun H => M.eval H) (fun H => decide (d ∈ M.queried H))
  have hsplitF := condProb_gate_split (cyl (∅ : Finset D) σ)
    (fun H => M.eval H) (fun H => decide (d ∈ M.queried H))
  -- The GOOD halves agree (reprogramming at `φ := id`).
  have hgood : condProb (cyl (insert d (∅ : Finset D)) (Function.update σ d c))
        (fun H => M.eval H && !decide (d ∈ M.queried H))
      = condProb (cyl (∅ : Finset D) σ)
        (fun H => M.eval H && !decide (d ∈ M.queried H)) := by
    have h := condProb_pin_untouched M (fun b => b) d ∅ σ c hd
    calc condProb (cyl (insert d (∅ : Finset D)) (Function.update σ d c))
          (fun H => M.eval H && !decide (d ∈ M.queried H))
        = condProb (cyl (insert d (∅ : Finset D)) (Function.update σ d c))
          (fun H => (fun b : Bool => b) (M.eval H) && !decide (d ∈ M.queried H)) :=
          condProb_congr (fun H _ => rfl)
      _ = condProb (cyl (∅ : Finset D) σ)
          (fun H => (fun b : Bool => b) (M.eval H) && !decide (d ∈ M.queried H)) := h
      _ = condProb (cyl (∅ : Finset D) σ)
          (fun H => M.eval H && !decide (d ∈ M.queried H)) :=
          condProb_congr (fun H _ => rfl)
  -- The BAD event has EQUAL mass in both worlds (reprogramming at `φ := const true`).
  have hnotbad : condProb (cyl (insert d (∅ : Finset D)) (Function.update σ d c))
        (fun H => !decide (d ∈ M.queried H))
      = condProb (cyl (∅ : Finset D) σ) (fun H => !decide (d ∈ M.queried H)) := by
    have h := condProb_pin_untouched M (fun _ => true) d ∅ σ c hd
    calc condProb (cyl (insert d (∅ : Finset D)) (Function.update σ d c))
          (fun H => !decide (d ∈ M.queried H))
        = condProb (cyl (insert d (∅ : Finset D)) (Function.update σ d c))
          (fun H => (fun _ : Bool => true) (M.eval H) && !decide (d ∈ M.queried H)) :=
          condProb_congr (fun H _ => by simp)
      _ = condProb (cyl (∅ : Finset D) σ)
          (fun H => (fun _ : Bool => true) (M.eval H) && !decide (d ∈ M.queried H)) := h
      _ = condProb (cyl (∅ : Finset D) σ) (fun H => !decide (d ∈ M.queried H)) :=
          condProb_congr (fun H _ => by simp)
  have hbad_eq : condProb (cyl (insert d (∅ : Finset D)) (Function.update σ d c))
        (fun H => decide (d ∈ M.queried H))
      = condProb (cyl (∅ : Finset D) σ) (fun H => decide (d ∈ M.queried H)) := by
    have h1P := condProb_gate_split (cyl (insert d (∅ : Finset D)) (Function.update σ d c))
      (fun _ => true) (fun H => decide (d ∈ M.queried H))
    have h1F := condProb_gate_split (cyl (∅ : Finset D) σ)
      (fun _ => true) (fun H => decide (d ∈ M.queried H))
    have honeP : condProb (cyl (insert d (∅ : Finset D)) (Function.update σ d c))
        (fun _ => true) = 1 :=
      condProb_eq_one (fun _ _ => rfl) (cyl_nonempty _ _)
    have honeF : condProb (cyl (∅ : Finset D) σ) (fun _ => true) = 1 :=
      condProb_eq_one (fun _ _ => rfl) (cyl_nonempty _ _)
    have hcP : condProb (cyl (insert d (∅ : Finset D)) (Function.update σ d c))
        (fun H => true && decide (d ∈ M.queried H))
        = condProb (cyl (insert d (∅ : Finset D)) (Function.update σ d c))
          (fun H => decide (d ∈ M.queried H)) :=
      condProb_congr (fun H _ => by simp)
    have hcP' : condProb (cyl (insert d (∅ : Finset D)) (Function.update σ d c))
        (fun H => true && !decide (d ∈ M.queried H))
        = condProb (cyl (insert d (∅ : Finset D)) (Function.update σ d c))
          (fun H => !decide (d ∈ M.queried H)) :=
      condProb_congr (fun H _ => by simp)
    have hcF : condProb (cyl (∅ : Finset D) σ)
        (fun H => true && decide (d ∈ M.queried H))
        = condProb (cyl (∅ : Finset D) σ) (fun H => decide (d ∈ M.queried H)) :=
      condProb_congr (fun H _ => by simp)
    have hcF' : condProb (cyl (∅ : Finset D) σ)
        (fun H => true && !decide (d ∈ M.queried H))
        = condProb (cyl (∅ : Finset D) σ) (fun H => !decide (d ∈ M.queried H)) :=
      condProb_congr (fun H _ => by simp)
    rw [honeP, hcP, hcP'] at h1P
    rw [honeF, hcF, hcF'] at h1F
    linarith [hnotbad]
  -- Assemble: the difference is the difference of the bad halves, each within the bad mass.
  have hbadP_le : condProb (cyl (insert d (∅ : Finset D)) (Function.update σ d c))
        (fun H => M.eval H && decide (d ∈ M.queried H))
      ≤ condProb (cyl (insert d (∅ : Finset D)) (Function.update σ d c))
        (fun H => decide (d ∈ M.queried H)) :=
    condProb_le_of_imp (fun H _ hH => by
      simp only [Bool.and_eq_true] at hH
      exact hH.2)
  have hbadF_le : condProb (cyl (∅ : Finset D) σ)
        (fun H => M.eval H && decide (d ∈ M.queried H))
      ≤ condProb (cyl (∅ : Finset D) σ) (fun H => decide (d ∈ M.queried H)) :=
    condProb_le_of_imp (fun H _ hH => by
      simp only [Bool.and_eq_true] at hH
      exact hH.2)
  have hbadP_nn := condProb_nonneg (cyl (insert d (∅ : Finset D)) (Function.update σ d c))
    (fun H => M.eval H && decide (d ∈ M.queried H))
  have hbadF_nn := condProb_nonneg (cyl (∅ : Finset D) σ)
    (fun H => M.eval H && decide (d ∈ M.queried H))
  rw [abs_sub_le_iff]
  constructor <;> linarith [hbad_eq, hgood, hsplitP, hsplitF, hbadP_le, hbadF_le,
    hbadP_nn, hbadF_nn]

end Reprogram

/-! ## §2 — the HIDING GAME over the keyed random oracle.

Message space `Msg` (the fixed-width span digests — equal length BY TYPE), blinding space `B`
(the prompt's "R": the hidden uniform blinding the challenger samples AFTER the adversary is
fixed), digest space `R`. The oracle domain is `Msg × B` — "the message concatenated with the
blinding" — mirroring `KeyedRomFamily.toRomFamily`'s tag-fold. -/

section Hiding

variable {Msg B R : Type}
variable [Fintype Msg] [DecidableEq Msg] [Fintype B] [DecidableEq B]
variable [Fintype R] [DecidableEq R] [Nonempty B] [Nonempty R]

/-- **A RAW HIDING DISTINGUISHER.** Two messages, fixed up front, and an `accept` verdict that —
at the RAW (unrestricted) type — may read the WHOLE experiment tape: the entire oracle `H` and
even the hidden blinding `r`, plus the challenge digest `c`. That maximal type is deliberate,
exactly as `FloorGames.Adversary` hands over the whole instance: the class `QueryHiding` below is
the restriction with content, and §5's `topAdv` shows what the raw type can do that the class
cannot. ONE `accept`, applied in both worlds — the `FloorGames.Distinguisher` discipline, so the
advantage is a genuine two-world gap. -/
structure HidingDistinguisher (Msg B R : Type) where
  /-- The first challenge message (a span digest; width fixed by the TYPE). -/
  msg0 : Msg
  /-- The second challenge message. -/
  msg1 : Msg
  /-- The accept verdict: full oracle, blinding, challenge digest. Raw — unrestricted. -/
  accept : ((Msg × B) → R) → B → R → Bool

/-- The challenged message in world `b`. -/
def HidingDistinguisher.msgAt (A : HidingDistinguisher Msg B R) : Bool → Msg
  | false => A.msg0
  | true => A.msg1

/-- **THE ACCEPT PROBABILITY IN WORLD `b`.** The challenger samples `H` uniform over
`Msg × B → R` and the blinding `r` uniform over `B` — both AFTER `A` is fixed (they are bound
variables of this definition; `A` is a parameter) — and hands `A` the challenge
`H (msgAt b, r)`. The deployed blinded-commitment shape. -/
noncomputable def acceptProb (A : HidingDistinguisher Msg B R) (b : Bool) : ℝ :=
  (∑ r : B, winProb (fun H : (Msg × B) → R => A.accept H r (H (A.msgAt b, r))))
    / (Fintype.card B : ℝ)

/-- **THE HIDING ADVANTAGE** — the difference of the two worlds' accept probabilities. A genuine
distinguishing gap (`FloorGames.distAdv`-shaped), NOT a `winProb`; `FloorGames` §7 records why
that matters. -/
noncomputable def hidingAdv (A : HidingDistinguisher Msg B R) : ℝ :=
  |acceptProb A false - acceptProb A true|

/-- The accept probability is a genuine probability. -/
theorem acceptProb_mem_unit (A : HidingDistinguisher Msg B R) (b : Bool) :
    0 ≤ acceptProb A b ∧ acceptProb A b ≤ 1 := by
  have hB : (0 : ℝ) < (Fintype.card B : ℝ) := by exact_mod_cast Fintype.card_pos
  constructor
  · unfold acceptProb
    have : (0 : ℝ) ≤ ∑ r : B, winProb (fun H : (Msg × B) → R => A.accept H r (H (A.msgAt b, r))) :=
      Finset.sum_nonneg (fun r _ => winProb_nonneg _)
    positivity
  · unfold acceptProb
    rw [div_le_one hB]
    calc (∑ r : B, winProb (fun H : (Msg × B) → R => A.accept H r (H (A.msgAt b, r))))
        ≤ ∑ _r : B, (1 : ℝ) := Finset.sum_le_sum (fun r _ => winProb_le_one _)
      _ = (Fintype.card B : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-- The hiding advantage is a real in `[0, 1]` (mirror of `FloorGames.distAdv_mem_unit`). -/
theorem hidingAdv_mem_unit (A : HidingDistinguisher Msg B R) :
    0 ≤ hidingAdv A ∧ hidingAdv A ≤ 1 := by
  refine ⟨abs_nonneg _, ?_⟩
  have h0 := acceptProb_mem_unit A false
  have h1 := acceptProb_mem_unit A true
  unfold hidingAdv
  rw [abs_sub_le_iff]
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2]

/-- **⚑ THE QUERY-BOUNDED KEYED CLASS — the `Eff` with content.** `A` FACTORS THROUGH a
challenge-indexed `Q`-query tree: its verdict is a function of the challenge digest and the
oracle answers it asked for — NOT of the raw oracle, and NOT of the hidden blinding `r`. The tree
is fixed before the oracle and the blinding are sampled (`acceptProb` samples both under the
quantifier), which is the `KeyedRomFloor` discipline that defeats hardcoding. -/
def QueryHiding (Q : ℕ) (A : HidingDistinguisher Msg B R) : Prop :=
  ∃ M : R → OracleComp (Msg × B) R Bool,
    (∀ c, QueryBounded Q (M c)) ∧
    ∀ (H : (Msg × B) → R) (r : B) (c : R), A.accept H r c = (M c).eval H

/-! ## §3 — the union bound: a `Q`-query tree touches the hidden blinding with mass `≤ Q/|B|`. -/

/-- **THE UNION BOUND OVER THE HIDDEN BLINDING.** A `Q`-query tree queries at most `Q` points per
run (`QueryBounded.queried_length_le`), so at most `Q` blinding values `r` can have their
challenge point `(m, r)` queried — summed over all `r`, the touch probability is at most `Q`.
Double counting over the finite oracle space; no probability theory beyond counting. -/
theorem sum_touch_le (M : OracleComp (Msg × B) R Bool) (Q : ℕ) (hM : QueryBounded Q M)
    (m : Msg) :
    (∑ r : B, winProb (fun H : (Msg × B) → R => decide ((m, r) ∈ M.queried H))) ≤ (Q : ℝ) := by
  classical
  have hN : (0 : ℝ) < (Fintype.card ((Msg × B) → R) : ℝ) := by exact_mod_cast Fintype.card_pos
  -- Per-oracle: at most `Q` blinding values are touched.
  have hcount : ∀ H : (Msg × B) → R,
      (Finset.univ.filter (fun r : B => decide ((m, r) ∈ M.queried H) = true)).card ≤ Q := by
    intro H
    calc (Finset.univ.filter (fun r : B => decide ((m, r) ∈ M.queried H) = true)).card
        ≤ (M.queried H).toFinset.card := by
          refine Finset.card_le_card_of_injOn (fun r => (m, r)) (fun r hr => ?_) ?_
          · have h2 := (Finset.mem_filter.1 hr).2
            exact List.mem_toFinset.2 (of_decide_eq_true h2)
          · intro r₁ _ r₂ _ h
            exact congrArg Prod.snd h
      _ ≤ (M.queried H).length := (M.queried H).toFinset_card_le
      _ ≤ Q := hM.queried_length_le H
  -- Double counting.
  have hkey : (∑ r : B, (Finset.univ.filter
        (fun H : (Msg × B) → R => decide ((m, r) ∈ M.queried H) = true)).card)
      ≤ Fintype.card ((Msg × B) → R) * Q := by
    have hswap : (∑ r : B, (Finset.univ.filter
          (fun H : (Msg × B) → R => decide ((m, r) ∈ M.queried H) = true)).card)
        = ∑ H : (Msg × B) → R, (Finset.univ.filter
          (fun r : B => decide ((m, r) ∈ M.queried H) = true)).card := by
      simp only [Finset.card_filter]
      exact Finset.sum_comm
    rw [hswap]
    calc (∑ H : (Msg × B) → R, (Finset.univ.filter
          (fun r : B => decide ((m, r) ∈ M.queried H) = true)).card)
        ≤ ∑ _H : (Msg × B) → R, Q := Finset.sum_le_sum (fun H _ => hcount H)
      _ = Fintype.card ((Msg × B) → R) * Q := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  -- Divide.
  have hterm : ∀ r : B,
      winProb (fun H : (Msg × B) → R => decide ((m, r) ∈ M.queried H))
        = ((Finset.univ.filter
            (fun H : (Msg × B) → R => decide ((m, r) ∈ M.queried H) = true)).card : ℝ)
          / (Fintype.card ((Msg × B) → R) : ℝ) := fun r => rfl
  rw [Finset.sum_congr rfl (fun r _ => hterm r), ← Finset.sum_div, div_le_iff₀ hN]
  calc (∑ r : B, ((Finset.univ.filter
        (fun H : (Msg × B) → R => decide ((m, r) ∈ M.queried H) = true)).card : ℝ))
      = ((∑ r : B, (Finset.univ.filter
          (fun H : (Msg × B) → R => decide ((m, r) ∈ M.queried H) = true)).card : ℕ) : ℝ) := by
        push_cast; rfl
    _ ≤ ((Fintype.card ((Msg × B) → R) * Q : ℕ) : ℝ) := by exact_mod_cast hkey
    _ = (Q : ℝ) * (Fintype.card ((Msg × B) → R) : ℝ) := by push_cast; ring

/-! ## §4 — ⚑ THE BOUND, PROVED: `hidingAdv ≤ 2·Q/|B|`. -/

/-- **THE CHALLENGE SPLIT.** Sampling the challenge digest IS splitting the oracle space on its
value at the challenge point — `condProb_split` at `S = ∅`, the lazy-sampling step. After the
split the pinned world runs the FIXED tree `M c` (the pin substitutes the challenge into the
tree's index), which is what §1's reprogramming lemma can then compare to the free world. -/
theorem winProb_challenge_split (M : R → OracleComp (Msg × B) R Bool) (d : Msg × B) :
    winProb (fun H : (Msg × B) → R => (M (H d)).eval H)
      = (∑ c : R, condProb
          (cyl (insert d (∅ : Finset (Msg × B)))
            (Function.update (fun _ => Classical.arbitrary R) d c))
          (fun H => (M c).eval H)) / (Fintype.card R : ℝ) := by
  rw [← condProb_cyl_empty (fun _ => Classical.arbitrary R)
    (fun H : (Msg × B) → R => (M (H d)).eval H)]
  rw [condProb_split (∅ : Finset (Msg × B)) (fun _ => Classical.arbitrary R) d (by simp)]
  congr 1
  refine Finset.sum_congr rfl (fun c _ => ?_)
  refine condProb_congr (fun H hH => ?_)
  have hpin : H d = c := by
    have := (mem_cyl.1 hH) d (Finset.mem_insert_self d ∅)
    simpa using this
  rw [hpin]

/-- **THE REAL-VS-HYBRID HOP AT ONE BLINDING.** The real acceptance at challenge point `d` differs
from the challenge-independent hybrid `(∑_c Pr[M c accepts])/|R|` by at most the averaged bad-event
mass — `condProb_pin_diff_le`, averaged over the sampled challenge. -/
theorem winProb_pin_dev (M : R → OracleComp (Msg × B) R Bool) (d : Msg × B) :
    |winProb (fun H : (Msg × B) → R => (M (H d)).eval H)
        - (∑ c : R, winProb (fun H : (Msg × B) → R => (M c).eval H)) / (Fintype.card R : ℝ)|
      ≤ (∑ c : R, winProb (fun H : (Msg × B) → R => decide (d ∈ (M c).queried H)))
          / (Fintype.card R : ℝ) := by
  have hRpos : (0 : ℝ) < (Fintype.card R : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [winProb_challenge_split M d, div_sub_div_same, abs_div,
    abs_of_pos hRpos, div_le_div_iff_of_pos_right hRpos, ← Finset.sum_sub_distrib]
  calc |∑ c : R, (condProb
          (cyl (insert d (∅ : Finset (Msg × B)))
            (Function.update (fun _ => Classical.arbitrary R) d c))
          (fun H => (M c).eval H)
        - winProb (fun H : (Msg × B) → R => (M c).eval H))|
      ≤ ∑ c : R, |condProb
          (cyl (insert d (∅ : Finset (Msg × B)))
            (Function.update (fun _ => Classical.arbitrary R) d c))
          (fun H => (M c).eval H)
        - winProb (fun H : (Msg × B) → R => (M c).eval H)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ c : R, winProb (fun H : (Msg × B) → R => decide (d ∈ (M c).queried H)) := by
        refine Finset.sum_le_sum (fun c _ => ?_)
        have h := condProb_pin_diff_le (M c) d (fun _ => Classical.arbitrary R) c
        rw [condProb_cyl_empty, condProb_cyl_empty] at h
        -- §1 synthesized the bad event's `Decidable` through `[DecidableEq D]` at abstract `D`;
        -- at the concrete product domain this section's statements synthesize it through
        -- `instBEqProd`. Propositionally the same event; bridge the `decide` instances.
        refine le_trans h (le_of_eq ?_)
        congr 1

/-- **THE PER-WORLD HYBRID DISTANCE:** in world `b`, the accept probability is within `Q/|B|` of
the `b`-INDEPENDENT hybrid `(∑_c Pr[M c accepts])/|R|`. The union bound over the hidden uniform
blinding pays for the bad event. -/
theorem acceptProb_dev_le (A : HidingDistinguisher Msg B R) (Q : ℕ)
    (M : R → OracleComp (Msg × B) R Bool)
    (hQb : ∀ c, QueryBounded Q (M c))
    (hrun : ∀ (H : (Msg × B) → R) (r : B) (c : R), A.accept H r c = (M c).eval H) (b : Bool) :
    |acceptProb A b
        - (∑ c : R, winProb (fun H : (Msg × B) → R => (M c).eval H)) / (Fintype.card R : ℝ)|
      ≤ (Q : ℝ) / (Fintype.card B : ℝ) := by
  have hBpos : (0 : ℝ) < (Fintype.card B : ℝ) := by exact_mod_cast Fintype.card_pos
  have hRpos : (0 : ℝ) < (Fintype.card R : ℝ) := by exact_mod_cast Fintype.card_pos
  set P : ℝ := (∑ c : R, winProb (fun H : (Msg × B) → R => (M c).eval H)) / (Fintype.card R : ℝ)
    with hP
  -- The adversary's verdict IS its tree's verdict.
  have hAcc : acceptProb A b
      = (∑ r : B, winProb (fun H : (Msg × B) → R => (M (H (A.msgAt b, r))).eval H))
        / (Fintype.card B : ℝ) := by
    unfold acceptProb
    congr 1
    refine Finset.sum_congr rfl (fun r _ => ?_)
    congr 1
    funext H
    rw [hrun]
  rw [hAcc]
  -- Difference of averages is the average of differences.
  have hdiff : (∑ r : B, winProb (fun H : (Msg × B) → R => (M (H (A.msgAt b, r))).eval H))
        / (Fintype.card B : ℝ) - P
      = (∑ r : B, (winProb (fun H : (Msg × B) → R => (M (H (A.msgAt b, r))).eval H) - P))
        / (Fintype.card B : ℝ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, sub_div,
      mul_comm (Fintype.card B : ℝ) P, mul_div_assoc, div_self (ne_of_gt hBpos), mul_one]
  rw [hdiff, abs_div, abs_of_pos hBpos, div_le_div_iff_of_pos_right hBpos]
  calc |∑ r : B, (winProb (fun H : (Msg × B) → R => (M (H (A.msgAt b, r))).eval H) - P)|
      ≤ ∑ r : B, |winProb (fun H : (Msg × B) → R => (M (H (A.msgAt b, r))).eval H) - P| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r : B, (∑ c : R, winProb
          (fun H : (Msg × B) → R => decide ((A.msgAt b, r) ∈ (M c).queried H)))
          / (Fintype.card R : ℝ) := by
        refine Finset.sum_le_sum (fun r _ => ?_)
        rw [hP]
        exact winProb_pin_dev M (A.msgAt b, r)
    _ ≤ (Q : ℝ) := by
        rw [← Finset.sum_div, Finset.sum_comm, div_le_iff₀ hRpos]
        calc (∑ c : R, ∑ r : B, winProb
              (fun H : (Msg × B) → R => decide ((A.msgAt b, r) ∈ (M c).queried H)))
            ≤ ∑ _c : R, (Q : ℝ) :=
              Finset.sum_le_sum (fun c _ => sum_touch_le (M c) Q (hQb c) (A.msgAt b))
          _ = (Fintype.card R : ℝ) * (Q : ℝ) := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          _ = (Q : ℝ) * (Fintype.card R : ℝ) := by ring

/-- **⚑⚑ THE KEYED-ROM HIDING BOUND — PROVED, information-theoretic.**

    For every `Q`-query keyed adversary:   `hidingAdv A ≤ 2·Q / |B|`

Two hybrid hops through the challenge-independent world (`acceptProb_dev_le` at `b = false` and
`b = true`; in the hybrid the view carries NO information about `b`, so the hybrids coincide —
they are literally the same real number). NOTHING is assumed: like `RomQueryFloor.birthday_bound`
this is a counting statement about the finite function space `Msg × B → R`, and its whole content
is that what the adversary has not queried, it does not know. The blinding `r` is never revealed;
only its `≤ Q` chances of being queried are paid for. -/
theorem hidingAdv_le (A : HidingDistinguisher Msg B R) (Q : ℕ) (hA : QueryHiding Q A) :
    hidingAdv A ≤ 2 * (Q : ℝ) / (Fintype.card B : ℝ) := by
  obtain ⟨M, hQb, hrun⟩ := hA
  have h0 := acceptProb_dev_le A Q M hQb hrun false
  have h1 := acceptProb_dev_le A Q M hQb hrun true
  set P : ℝ := (∑ c : R, winProb (fun H : (Msg × B) → R => (M c).eval H)) / (Fintype.card R : ℝ)
  unfold hidingAdv
  calc |acceptProb A false - acceptProb A true|
      ≤ |acceptProb A false - P| + |P - acceptProb A true| := abs_sub_le _ P _
    _ ≤ (Q : ℝ) / (Fintype.card B : ℝ) + (Q : ℝ) / (Fintype.card B : ℝ) := by
        have h1' : |P - acceptProb A true| ≤ (Q : ℝ) / (Fintype.card B : ℝ) := by
          rw [abs_sub_comm]; exact h1
        exact add_le_add h0 h1'
    _ = 2 * (Q : ℝ) / (Fintype.card B : ℝ) := by ring

/-- The bound in the cruder `(2Q + 1)/|B|` form (the shape the task states; the sharp constant is
`2Q`, `hidingAdv_le`). -/
theorem hidingAdv_le' (A : HidingDistinguisher Msg B R) (Q : ℕ) (hA : QueryHiding Q A) :
    hidingAdv A ≤ (2 * (Q : ℝ) + 1) / (Fintype.card B : ℝ) := by
  have hB : (0 : ℝ) < (Fintype.card B : ℝ) := by exact_mod_cast Fintype.card_pos
  refine (hidingAdv_le A Q hA).trans ?_
  rw [div_le_div_iff_of_pos_right hB]
  linarith

/-- **(TOOTH — the HARDCODER is DEFANGED, not excluded.)** A `0`-query adversary — the exact shape
that refutes the `IsPolyTime` floors by hardcoding a fixed answer — is ADMITTED by the class, and
its advantage is EXACTLY `0`: with no queries, its verdict is a function of the challenge digest
alone, and the challenge digest's distribution is identical in both worlds. Sampling the blinding
AFTER the adversary is fixed is what makes hardcoding worthless — the
`KeyedRomFloor.fixedPairAdv_negl` story, on the hiding side, with an even sharper constant. -/
theorem zeroQuery_hidingAdv_eq_zero (A : HidingDistinguisher Msg B R)
    (hA : QueryHiding 0 A) : hidingAdv A = 0 := by
  have h := hidingAdv_le A 0 hA
  have h0 : (2 : ℝ) * ((0 : ℕ) : ℝ) / (Fintype.card B : ℝ) = 0 := by norm_num
  rw [h0] at h
  exact le_antisymm h (abs_nonneg _)

/-! ## §5 — ⚑ THE `⊤` POLE: the unrestricted adversary WINS the hiding game. -/

/-- **THE FULL-TAPE ADVERSARY.** It reads ALL of `H` and the actual blinding `r` — legal at the
raw `accept` type, impossible for a query tree — recomputes `H (msg0, r)`, and accepts iff the
challenge equals it. In world `false` it is always right; in world `true` it is fooled only when
the two challenge points collide. -/
def topAdv (m0 m1 : Msg) : HidingDistinguisher Msg B R where
  msg0 := m0
  msg1 := m1
  accept := fun H r c => decide (c = H (m0, r))

/-- The full-tape adversary accepts world `false` with certainty. -/
theorem topAdv_acceptProb_false (m0 m1 : Msg) :
    acceptProb (topAdv (B := B) (R := R) m0 m1) false = 1 := by
  have hBpos : (0 : ℝ) < (Fintype.card B : ℝ) := by exact_mod_cast Fintype.card_pos
  unfold acceptProb
  have hterm : ∀ r : B, winProb (fun H : (Msg × B) → R =>
      (topAdv (B := B) (R := R) m0 m1).accept H r
        (H ((topAdv (B := B) (R := R) m0 m1).msgAt false, r))) = 1 := by
    intro r
    have hpred : (fun H : (Msg × B) → R =>
        (topAdv (B := B) (R := R) m0 m1).accept H r
          (H ((topAdv (B := B) (R := R) m0 m1).msgAt false, r))) = fun _ => true := by
      funext H
      show decide (H (m0, r) = H (m0, r)) = true
      simp
    rw [hpred]
    exact winProb_top
  rw [Finset.sum_congr rfl (fun r _ => hterm r), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, div_self (ne_of_gt hBpos)]

/-- The full-tape adversary accepts world `true` with probability exactly `1/|R|` — the two
challenge points are distinct, and a uniform oracle collides them with exactly that mass
(`condProb_two_fresh_eq`). -/
theorem topAdv_acceptProb_true (m0 m1 : Msg) (hne : m0 ≠ m1) :
    acceptProb (topAdv (B := B) (R := R) m0 m1) true = 1 / (Fintype.card R : ℝ) := by
  have hBpos : (0 : ℝ) < (Fintype.card B : ℝ) := by exact_mod_cast Fintype.card_pos
  unfold acceptProb
  have hterm : ∀ r : B, winProb (fun H : (Msg × B) → R =>
      (topAdv (B := B) (R := R) m0 m1).accept H r
        (H ((topAdv (B := B) (R := R) m0 m1).msgAt true, r)))
      = 1 / (Fintype.card R : ℝ) := by
    intro r
    have hpred : (fun H : (Msg × B) → R =>
        (topAdv (B := B) (R := R) m0 m1).accept H r
          (H ((topAdv (B := B) (R := R) m0 m1).msgAt true, r)))
        = fun H : (Msg × B) → R => decide (H (m1, r) = H (m0, r)) := rfl
    rw [hpred]
    have hxy : ((m1 : Msg), r) ≠ ((m0 : Msg), r) := by
      intro h
      exact hne (congrArg Prod.fst h).symm
    have h := condProb_two_fresh_eq (D := Msg × B) (R := R) ∅
      (fun _ => Classical.arbitrary R) (m1, r) (m0, r) (by simp) (by simp) hxy
    rwa [condProb_cyl_empty] at h
  rw [Finset.sum_congr rfl (fun r _ => hterm r), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_comm, mul_div_assoc, div_self (ne_of_gt hBpos), mul_one]

/-- **⚑ THE `⊤` POLE, EXACTLY PRICED: the unrestricted adversary's advantage is `1 − 1/|R|`.**
The hiding floor is NOT vacuously true — remove the query bound and hiding is broken (at any
digest space with more than one element, this is `≥ 1/2`). The keyed-ROM analogue of
`RomQueryFloor.romCollision_top_false`'s role: same game, unrestricted class, opposite verdict. -/
theorem topAdv_hidingAdv (m0 m1 : Msg) (hne : m0 ≠ m1) :
    hidingAdv (topAdv (B := B) (R := R) m0 m1) = 1 - 1 / (Fintype.card R : ℝ) := by
  have hR1 : (1 : ℝ) ≤ (Fintype.card R : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := R)
  have hinv : 1 / (Fintype.card R : ℝ) ≤ 1 := by
    rw [div_le_one (by linarith)]
    exact hR1
  unfold hidingAdv
  rw [topAdv_acceptProb_false m0 m1, topAdv_acceptProb_true m0 m1 hne,
    abs_of_nonneg (by linarith)]

/-! ## §6 — the `⊥` pole: a REAL one-query distinguisher, in the class, really winning. -/

/-- **A REAL ONE-QUERY DISTINGUISHER.** It fixes a blinding guess `r₀`, queries the single point
`(msg0, r₀)`, and accepts iff the answer equals the challenge. When the sampled blinding happens
to hit `r₀` (probability `1/|B|`) it identifies world `false` with certainty. -/
def oneQueryAdv (m0 m1 : Msg) (r0 : B) : HidingDistinguisher Msg B R where
  msg0 := m0
  msg1 := m1
  accept := fun H _r c => decide (H (m0, r0) = c)

/-- **THE ONE-QUERY DISTINGUISHER IS IN THE CLASS** — it factors through a genuine one-query tree
(query `(msg0, r₀)`, compare with the challenge). The class is inhabited by an adversary that
really queries. -/
theorem oneQueryAdv_queryHiding (m0 m1 : Msg) (r0 : B) (Q : ℕ) (hQ : 1 ≤ Q) :
    QueryHiding Q (oneQueryAdv (B := B) (R := R) m0 m1 r0) := by
  refine ⟨fun c => .query (m0, r0) (fun a => .pure (decide (a = c))), fun c => ?_, ?_⟩
  · exact (QueryBounded.query 0 (m0, r0) _
      (fun a => QueryBounded.pure 0 _)).mono hQ
  · intro H r c
    show decide (H (m0, r0) = c) = decide (H (m0, r0) = c)
    rfl

/-- The one-query distinguisher's world-`false` accept probability, exactly:
`(1 + (|B| − 1)/|R|) / |B|` — certainty when the blinding guess hits, `1/|R|` otherwise. -/
theorem oneQueryAdv_acceptProb_false (m0 m1 : Msg) (r0 : B) :
    acceptProb (oneQueryAdv (B := B) (R := R) m0 m1 r0) false
      = (1 + ((Fintype.card B : ℝ) - 1) / (Fintype.card R : ℝ)) / (Fintype.card B : ℝ) := by
  unfold acceptProb
  congr 1
  have hsplit : (∑ r : B, winProb (fun H : (Msg × B) → R =>
      (oneQueryAdv (B := B) (R := R) m0 m1 r0).accept H r
        (H ((oneQueryAdv (B := B) (R := R) m0 m1 r0).msgAt false, r))))
      = winProb (fun H : (Msg × B) → R =>
          (oneQueryAdv (B := B) (R := R) m0 m1 r0).accept H r0
            (H ((oneQueryAdv (B := B) (R := R) m0 m1 r0).msgAt false, r0)))
        + ∑ r ∈ Finset.univ.erase r0, winProb (fun H : (Msg × B) → R =>
            (oneQueryAdv (B := B) (R := R) m0 m1 r0).accept H r
              (H ((oneQueryAdv (B := B) (R := R) m0 m1 r0).msgAt false, r))) :=
    (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ r0)).symm
  rw [hsplit]
  -- The hit term: probability 1.
  have hhit : winProb (fun H : (Msg × B) → R =>
      (oneQueryAdv (B := B) (R := R) m0 m1 r0).accept H r0
        (H ((oneQueryAdv (B := B) (R := R) m0 m1 r0).msgAt false, r0))) = 1 := by
    have hpred : (fun H : (Msg × B) → R =>
        (oneQueryAdv (B := B) (R := R) m0 m1 r0).accept H r0
          (H ((oneQueryAdv (B := B) (R := R) m0 m1 r0).msgAt false, r0))) = fun _ => true := by
      funext H
      show decide (H (m0, r0) = H (m0, r0)) = true
      simp
    rw [hpred]
    exact winProb_top
  -- The miss terms: probability `1/|R|` each.
  have hmiss : ∀ r ∈ Finset.univ.erase r0,
      winProb (fun H : (Msg × B) → R =>
        (oneQueryAdv (B := B) (R := R) m0 m1 r0).accept H r
          (H ((oneQueryAdv (B := B) (R := R) m0 m1 r0).msgAt false, r)))
        = 1 / (Fintype.card R : ℝ) := by
    intro r hr
    have hrne : r ≠ r0 := (Finset.mem_erase.1 hr).1
    have hpred : (fun H : (Msg × B) → R =>
        (oneQueryAdv (B := B) (R := R) m0 m1 r0).accept H r
          (H ((oneQueryAdv (B := B) (R := R) m0 m1 r0).msgAt false, r)))
        = fun H : (Msg × B) → R => decide (H (m0, r0) = H (m0, r)) := rfl
    rw [hpred]
    have hxy : ((m0 : Msg), r0) ≠ ((m0 : Msg), r) := by
      intro h
      exact hrne (congrArg Prod.snd h).symm
    have h := condProb_two_fresh_eq (D := Msg × B) (R := R) ∅
      (fun _ => Classical.arbitrary R) (m0, r0) (m0, r) (by simp) (by simp) hxy
    rwa [condProb_cyl_empty] at h
  rw [hhit, Finset.sum_congr rfl hmiss, Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ r0), Finset.card_univ, nsmul_eq_mul]
  have hB1 : (1 : ℕ) ≤ Fintype.card B := Fintype.card_pos
  push_cast [hB1]
  ring

/-- The one-query distinguisher's world-`true` accept probability is exactly `1/|R|` — its probe
point and the challenge point differ in the message coordinate at EVERY blinding. -/
theorem oneQueryAdv_acceptProb_true (m0 m1 : Msg) (r0 : B) (hne : m0 ≠ m1) :
    acceptProb (oneQueryAdv (B := B) (R := R) m0 m1 r0) true = 1 / (Fintype.card R : ℝ) := by
  have hBpos : (0 : ℝ) < (Fintype.card B : ℝ) := by exact_mod_cast Fintype.card_pos
  unfold acceptProb
  have hterm : ∀ r : B, winProb (fun H : (Msg × B) → R =>
      (oneQueryAdv (B := B) (R := R) m0 m1 r0).accept H r
        (H ((oneQueryAdv (B := B) (R := R) m0 m1 r0).msgAt true, r)))
      = 1 / (Fintype.card R : ℝ) := by
    intro r
    have hpred : (fun H : (Msg × B) → R =>
        (oneQueryAdv (B := B) (R := R) m0 m1 r0).accept H r
          (H ((oneQueryAdv (B := B) (R := R) m0 m1 r0).msgAt true, r)))
        = fun H : (Msg × B) → R => decide (H (m0, r0) = H (m1, r)) := rfl
    rw [hpred]
    have hxy : ((m0 : Msg), r0) ≠ ((m1 : Msg), r) := by
      intro h
      exact hne (congrArg Prod.fst h)
    have h := condProb_two_fresh_eq (D := Msg × B) (R := R) ∅
      (fun _ => Classical.arbitrary R) (m0, r0) (m1, r) (by simp) (by simp) hxy
    rwa [condProb_cyl_empty] at h
  rw [Finset.sum_congr rfl (fun r _ => hterm r), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_comm, mul_div_assoc, div_self (ne_of_gt hBpos), mul_one]

/-- **⚑ THE `⊥` POLE, EXACTLY PRICED: the one-query distinguisher's advantage is
`(1 − 1/|R|)/|B|`.** Inside the `2·1/|B|` bound, and REAL. -/
theorem oneQueryAdv_hidingAdv (m0 m1 : Msg) (r0 : B) (hne : m0 ≠ m1) :
    hidingAdv (oneQueryAdv (B := B) (R := R) m0 m1 r0)
      = (1 - 1 / (Fintype.card R : ℝ)) / (Fintype.card B : ℝ) := by
  have hBpos : (0 : ℝ) < (Fintype.card B : ℝ) := by exact_mod_cast Fintype.card_pos
  have hRpos : (0 : ℝ) < (Fintype.card R : ℝ) := by exact_mod_cast Fintype.card_pos
  unfold hidingAdv
  rw [oneQueryAdv_acceptProb_false m0 m1 r0, oneQueryAdv_acceptProb_true m0 m1 r0 hne]
  have hval : (1 + ((Fintype.card B : ℝ) - 1) / (Fintype.card R : ℝ)) / (Fintype.card B : ℝ)
      - 1 / (Fintype.card R : ℝ)
      = (1 - 1 / (Fintype.card R : ℝ)) / (Fintype.card B : ℝ) := by
    field_simp
    ring
  rw [hval, abs_of_nonneg]
  have hinv : 1 / (Fintype.card R : ℝ) ≤ 1 := by
    rw [div_le_one hRpos]
    exact_mod_cast Fintype.card_pos (α := R)
  positivity

/-- **(TOOTH — NON-VACUITY WITNESS.)** With a genuine digest space (`|R| > 1`), the one-query
distinguisher's advantage is strictly POSITIVE: the class contains an attack that really runs,
really queries, and really wins sometimes — so `hidingAdv_le` is a statement about something.
Mirror of `RomQueryFloor.twoPointAdv_gameAdv_pos`. -/
theorem oneQueryAdv_hidingAdv_pos (m0 m1 : Msg) (r0 : B) (hne : m0 ≠ m1)
    (hR : 1 < Fintype.card R) :
    0 < hidingAdv (oneQueryAdv (B := B) (R := R) m0 m1 r0) := by
  rw [oneQueryAdv_hidingAdv m0 m1 r0 hne]
  have hBpos : (0 : ℝ) < (Fintype.card B : ℝ) := by exact_mod_cast Fintype.card_pos
  have hR' : (1 : ℝ) < (Fintype.card R : ℝ) := by exact_mod_cast hR
  have hnum : (0 : ℝ) < 1 - 1 / (Fintype.card R : ℝ) := by
    have : 1 / (Fintype.card R : ℝ) < 1 := by
      rw [div_lt_one (by linarith)]
      exact hR'
    linarith
  positivity

end Hiding

/-! ## §7 — THE CANARY, at one concrete instantiation.

`Msg = Fin 2`, `B = Fin 8`, `R = Fin 4`, budget `Q = 1`: the bound says a one-query adversary's
advantage is at most `2/8 = 1/4`. The UNRESTRICTED `topAdv` has advantage `3/4`. So the bound is
FALSE of the unbounded adversary — the theorem's class restriction is load-bearing, not
decoration — and `topAdv` is PROVABLY outside the one-query class. If either canary ever stops
failing/holding, the bound has degenerated. -/

/-- **(CANARY — the unbounded adversary does NOT satisfy the bound.)** -/
theorem canary_top_breaks_bound :
    ¬ (hidingAdv (topAdv (Msg := Fin 2) (B := Fin 8) (R := Fin 4) 0 1)
        ≤ 2 * ((1 : ℕ) : ℝ) / (Fintype.card (Fin 8) : ℝ)) := by
  rw [topAdv_hidingAdv (Msg := Fin 2) (B := Fin 8) (R := Fin 4) 0 1 (by decide)]
  simp only [Fintype.card_fin]
  norm_num

/-- **(CANARY — hence the full-tape adversary is NOT in the one-query class.)** The keyed-ROM
hiding analogue of `RomQueryFloor.choiceAdv_not_romEff`: the adversary that reads the whole
oracle would have to know answers it never asked for; here that exclusion is PRICED — its
advantage exceeds what any class member can achieve. -/
theorem canary_topAdv_not_oneQuery :
    ¬ QueryHiding 1 (topAdv (Msg := Fin 2) (B := Fin 8) (R := Fin 4) 0 1) := by
  intro h
  exact canary_top_breaks_bound (hidingAdv_le _ 1 h)

/-! ## §8 — the λ-indexed family layer: the FLOOR, in `FloorGames`' `∀ D, Eff D → Negl` shape. -/

/-- **A KEYED-ROM HIDING FAMILY.** At each security parameter: a finite message (span-digest)
space, a finite blinding space (the challenger's hidden uniform coin), and a finite digest
space. -/
structure HidingRomFamily where
  /-- The message space at parameter `l` — fixed-width span digests (equal length BY TYPE). -/
  Msg : ℕ → Type
  /-- The blinding space at parameter `l` — the hidden uniform blinding felt. -/
  B : ℕ → Type
  /-- The digest space at parameter `l`. -/
  R : ℕ → Type
  /-- The message space is finite. -/
  msgFin : ∀ l, Fintype (Msg l)
  /-- Decidable equality on messages. -/
  msgDec : ∀ l, DecidableEq (Msg l)
  /-- The message space is inhabited. -/
  msgNe : ∀ l, Nonempty (Msg l)
  /-- The blinding space is finite. -/
  bFin : ∀ l, Fintype (B l)
  /-- Decidable equality on blindings. -/
  bDec : ∀ l, DecidableEq (B l)
  /-- The blinding space is inhabited. -/
  bNe : ∀ l, Nonempty (B l)
  /-- The digest space is finite. -/
  rFin : ∀ l, Fintype (R l)
  /-- Decidable equality on digests. -/
  rDec : ∀ l, DecidableEq (R l)
  /-- The digest space is inhabited. -/
  rNe : ∀ l, Nonempty (R l)

/-- A family of raw hiding distinguishers, one per parameter. -/
structure FamilyHidingDistinguisher (F : HidingRomFamily) where
  /-- The distinguisher at parameter `l`. -/
  adv : ∀ l, HidingDistinguisher (F.Msg l) (F.B l) (F.R l)

/-- The family distinguisher's advantage ensemble. -/
noncomputable def famHidingAdv (F : HidingRomFamily) (A : FamilyHidingDistinguisher F) :
    Ensemble := fun l =>
  letI := F.msgFin l; letI := F.msgDec l; letI := F.bFin l; letI := F.bDec l
  letI := F.rFin l; letI := F.rDec l; letI := F.bNe l; letI := F.rNe l
  hidingAdv (A.adv l)

/-- **THE QUERY-BOUNDED KEYED CLASS, λ-indexed** — the `Eff` of the hiding floor: at each
parameter, the distinguisher factors through a `Q l`-query tree fixed before the oracle and
blinding are sampled. -/
def KeyedRomHidingEff (F : HidingRomFamily) (Q : ℕ → ℕ)
    (A : FamilyHidingDistinguisher F) : Prop :=
  ∀ l,
    letI := F.msgFin l; letI := F.msgDec l; letI := F.bFin l; letI := F.bDec l
    letI := F.rFin l; letI := F.rDec l; letI := F.bNe l; letI := F.rNe l
    QueryHiding (Q l) (A.adv l)

/-- **THE HIDING FLOOR SCHEMA** — `FloorGames.DecisionMLWEHardQuant`'s `∀ D, Eff D → Negl (distAdv)`
shape, at the keyed-ROM hiding game. -/
def HidingHard (F : HidingRomFamily) (Eff : FamilyHidingDistinguisher F → Prop) : Prop :=
  ∀ A : FamilyHidingDistinguisher F, Eff A → Negl (famHidingAdv F A)

/-- **⚑⚑ THE KEYED-ROM HIDING FLOOR, PROVED.** At a `λ`-bit blinding space (`|B l| = 2^l`) and a
polynomially bounded query budget, EVERY query-bounded keyed distinguisher's hiding advantage is
negligible. No cryptographic assumption anywhere under it — `hidingAdv_le` is counting, and the
`Negl` comes from `negl_two_pow`: the blinding space outruns the budget. The hiding twin of
`RomQueryFloor.romCollision_hard`. -/
theorem keyedRomHiding_hard (F : HidingRomFamily) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => 2 * (Q l : ℝ) + 1))
    (hw : ∀ l, letI := F.bFin l; Fintype.card (F.B l) = 2 ^ l) :
    HidingHard F (KeyedRomHidingEff F Q) := by
  intro A hA
  refine negl_of_eventually_le (Filter.Eventually.of_forall (fun l => ?_))
    (negl_mul_poly hQ negl_two_pow)
  letI := F.msgFin l; letI := F.msgDec l; letI := F.bFin l; letI := F.bDec l
  letI := F.rFin l; letI := F.rDec l; letI := F.bNe l; letI := F.rNe l
  have h0 : 0 ≤ famHidingAdv F A l := (hidingAdv_mem_unit (A.adv l)).1
  have hle : famHidingAdv F A l ≤ (2 * (Q l : ℝ) + 1) / ((2 ^ l : ℕ) : ℝ) := by
    have h := hidingAdv_le' (A.adv l) (Q l) (hA l)
    rwa [hw l] at h
  have hkey : (2 * (Q l : ℝ) + 1) * (1 / (2 : ℝ) ^ l)
      = (2 * (Q l : ℝ) + 1) / ((2 ^ l : ℕ) : ℝ) := by
    push_cast
    ring
  rw [abs_of_nonneg h0,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 * (Q l : ℝ) + 1) * (1 / (2 : ℝ) ^ l)), hkey]
  exact hle

/-- **⚑ THE UNRESTRICTED HIDING FLOOR IS FALSE** at any family whose digest space genuinely has
two elements: the full-tape `topAdv` family's advantage is `1 − 1/|R l| ≥ 1/2` at every
parameter, which is not negligible. Same game, two classes, opposite verdicts — the query bound
is doing real work, exactly as `RomQueryFloor.binaryRom_top_false` vs `binaryRom_hard`. -/
theorem hidingTop_false (F : HidingRomFamily)
    (hR : ∀ l, letI := F.rFin l; 2 ≤ Fintype.card (F.R l))
    (m0 m1 : ∀ l, F.Msg l) (hne : ∀ l, m0 l ≠ m1 l) :
    ¬ HidingHard F (fun _ => True) := by
  intro h
  have hnegl := h ⟨fun l =>
    letI := F.rDec l
    topAdv (B := F.B l) (R := F.R l) (m0 l) (m1 l)⟩ trivial
  have hge : ∀ l, (1 : ℝ) / 2 ≤ famHidingAdv F
      ⟨fun l =>
        letI := F.rDec l
        topAdv (B := F.B l) (R := F.R l) (m0 l) (m1 l)⟩ l := by
    intro l
    letI := F.msgFin l; letI := F.msgDec l; letI := F.bFin l; letI := F.bDec l
    letI := F.rFin l; letI := F.rDec l; letI := F.bNe l; letI := F.rNe l
    show (1 : ℝ) / 2 ≤ hidingAdv (topAdv (B := F.B l) (R := F.R l) (m0 l) (m1 l))
    rw [topAdv_hidingAdv (m0 l) (m1 l) (hne l)]
    have h2 : (2 : ℝ) ≤ (Fintype.card (F.R l) : ℝ) := by exact_mod_cast hR l
    have hinv : 1 / (Fintype.card (F.R l) : ℝ) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) h2
    linarith
  obtain ⟨l, hlt, hl2⟩ := ((hnegl 1).and (Filter.eventually_ge_atTop 2)).exists
  have hl2' : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl2
  have hnn : (0 : ℝ) ≤ famHidingAdv F
      ⟨fun l =>
        letI := F.rDec l
        topAdv (B := F.B l) (R := F.R l) (m0 l) (m1 l)⟩ l :=
    le_trans (by norm_num) (hge l)
  rw [abs_of_nonneg hnn, pow_one] at hlt
  have hinv : 1 / (l : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hl2'
  linarith [hge l]

/-! ## §9 — ⚑ THE RE-GROUNDING: span-hiding of the wide blinded commitment, at the PROVED floor.

`Metatheory.Open.BlindedSpanHiding` (Lane B, imported READ-ONLY) proved span hiding CONDITIONALLY
on `WidePreimageFloor (IsPolyTime …)` — and then proved that floor FALSE at deployed parameters
(`widePreimageFloor_polyTime_false`), naming the keyed query-counted class as the honest
successor and leaving the two-world indistinguishability form (§(c).1) OPEN. This section is that
successor: the deployed blinded-commitment shape — `hash(span_digest8 ‖ BLINDING)` with the
blinding a hidden uniform felt sampled after everything else is fixed — modeled with the wide
Poseidon2 as a keyed random oracle, at the deployed growth (a `λ`-bit blinding felt, a wide
digest), with the two-world hiding advantage BOUNDED and NEGLIGIBLE against every `Q`-query keyed
adversary. The named residual is the ROM-modeling of Poseidon2 — the same residual the collision
floor carries — NOT a refutable cost-model floor. -/

/-- **THE DEPLOYED-SHAPE BLINDED-SPAN FAMILY.** Span digests `Fin (2·2^l)` (at least two distinct
spans at every parameter; equal width BY TYPE), a `λ`-bit blinding felt `Fin (2^l)` (the deployed
one-felt `BLINDING`), and a wide digest `Fin (2^(8l+8))` (the deployed 8-felt digest, wider than
the blinding at every parameter). -/
def blindedSpanRomFamily : HidingRomFamily where
  Msg := fun l => Fin (2 * 2 ^ l)
  B := fun l => Fin (2 ^ l)
  R := fun l => Fin (2 ^ (8 * l + 8))
  msgFin := fun _ => inferInstance
  msgDec := fun _ => inferInstance
  msgNe := fun l => ⟨⟨0, by positivity⟩⟩
  bFin := fun _ => inferInstance
  bDec := fun _ => inferInstance
  bNe := fun l => ⟨⟨0, by positivity⟩⟩
  rFin := fun _ => inferInstance
  rDec := fun _ => inferInstance
  rNe := fun l => ⟨⟨0, by positivity⟩⟩

theorem blindedSpanRom_card_B (l : ℕ) :
    letI := blindedSpanRomFamily.bFin l
    Fintype.card (blindedSpanRomFamily.B l) = 2 ^ l := by
  show Fintype.card (Fin (2 ^ l)) = 2 ^ l
  simp

/-- **⚑ SPAN-HIDING OF THE WIDE BLINDED COMMITMENT — the per-parameter advantage bound.** Every
`Q l`-query keyed adversary distinguishing two committed spans has advantage at most
`(2·Q l + 1)/2^l` (sharp form `2·Q l/2^l`): the deployed wide blinded span commitment hides its
span except with that advantage, in the keyed ROM. The corollary Lane B's §(c).1 said the tree
could not yet state — stated, and PROVED. -/
theorem blindedSpanRom_hiding_bound (Q : ℕ → ℕ)
    (A : FamilyHidingDistinguisher blindedSpanRomFamily)
    (hA : KeyedRomHidingEff blindedSpanRomFamily Q A) (l : ℕ) :
    famHidingAdv blindedSpanRomFamily A l ≤ (2 * (Q l : ℝ) + 1) / (2 : ℝ) ^ l := by
  letI := blindedSpanRomFamily.msgFin l; letI := blindedSpanRomFamily.msgDec l
  letI := blindedSpanRomFamily.bFin l; letI := blindedSpanRomFamily.bDec l
  letI := blindedSpanRomFamily.rFin l; letI := blindedSpanRomFamily.rDec l
  letI := blindedSpanRomFamily.bNe l; letI := blindedSpanRomFamily.rNe l
  have h := hidingAdv_le' (A.adv l) (Q l) (hA l)
  rw [blindedSpanRom_card_B l] at h
  have hcast : ((2 ^ l : ℕ) : ℝ) = (2 : ℝ) ^ l := by push_cast; ring
  rwa [hcast] at h

/-- **⚑⚑ SPAN-HIDING, NEGLIGIBLE — the floor at the deployed shape.** For any polynomial query
budget, the keyed query-bounded hiding floor HOLDS at the deployed-shape blinded-span family. -/
theorem blindedSpanRom_hiding_negl (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => 2 * (Q l : ℝ) + 1)) :
    HidingHard blindedSpanRomFamily (KeyedRomHidingEff blindedSpanRomFamily Q) :=
  keyedRomHiding_hard blindedSpanRomFamily Q hQ blindedSpanRom_card_B

/-- **(TOOTH — the unrestricted floor at the SAME family is FALSE.)** -/
theorem blindedSpanRom_top_false :
    ¬ HidingHard blindedSpanRomFamily (fun _ => True) := by
  have hlt : ∀ l : ℕ, 1 < 2 * 2 ^ l := by
    intro l
    have : 0 < 2 ^ l := by positivity
    omega
  refine hidingTop_false blindedSpanRomFamily (fun l => ?_)
    (fun l => ⟨0, by have := hlt l; omega⟩) (fun l => ⟨1, hlt l⟩) (fun l h => ?_)
  · show 2 ≤ Fintype.card (Fin (2 ^ (8 * l + 8)))
    rw [Fintype.card_fin]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (8 * l + 8) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · have := congrArg Fin.val h
    simp at this

/-- **(TOOTH — the class at the deployed family is INHABITED by a real winner.)** The one-query
distinguisher has strictly positive advantage at every parameter — the floor is not `⊥` in
disguise. -/
theorem blindedSpanRom_inhabited (Q : ℕ → ℕ) (hQ : ∀ l, 1 ≤ Q l) :
    ∃ A : FamilyHidingDistinguisher blindedSpanRomFamily,
      KeyedRomHidingEff blindedSpanRomFamily Q A
        ∧ ∀ l, 0 < famHidingAdv blindedSpanRomFamily A l := by
  have hlt : ∀ l : ℕ, 1 < 2 * 2 ^ l := by
    intro l
    have : 0 < 2 ^ l := by positivity
    omega
  refine ⟨⟨fun l => oneQueryAdv (B := Fin (2 ^ l)) (R := Fin (2 ^ (8 * l + 8)))
      (⟨0, by have := hlt l; omega⟩ : Fin (2 * 2 ^ l)) (⟨1, hlt l⟩ : Fin (2 * 2 ^ l))
      (⟨0, by positivity⟩ : Fin (2 ^ l))⟩, fun l => ?_, fun l => ?_⟩
  · letI := blindedSpanRomFamily.msgFin l; letI := blindedSpanRomFamily.msgDec l
    letI := blindedSpanRomFamily.bFin l; letI := blindedSpanRomFamily.bDec l
    letI := blindedSpanRomFamily.rFin l; letI := blindedSpanRomFamily.rDec l
    letI := blindedSpanRomFamily.bNe l; letI := blindedSpanRomFamily.rNe l
    exact oneQueryAdv_queryHiding _ _ _ (Q l) (hQ l)
  · letI := blindedSpanRomFamily.msgFin l; letI := blindedSpanRomFamily.msgDec l
    letI := blindedSpanRomFamily.bFin l; letI := blindedSpanRomFamily.bDec l
    letI := blindedSpanRomFamily.rFin l; letI := blindedSpanRomFamily.rDec l
    letI := blindedSpanRomFamily.bNe l; letI := blindedSpanRomFamily.rNe l
    refine oneQueryAdv_hidingAdv_pos _ _ _ ?_ ?_
    · intro h
      have := congrArg Fin.val h
      simp at this
    · show 1 < Fintype.card (Fin (2 ^ (8 * l + 8)))
      rw [Fintype.card_fin]
      calc 1 < 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (8 * l + 8) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **(THE REPLACED FLOOR, RE-EXPORTED READ-ONLY.)** Lane B's own refutation: the
`WidePreimageFloor` at `IsPolyTime` — the floor its conditional span-hiding rested on — is FALSE
at every deployed commitment. This is the vacuity THIS file's floor replaces; pinned here so the
replacement is visible at the replacement site. -/
theorem laneB_polyTime_floor_refuted
    (D : Metatheory.Open.BlindedSpanHiding.BlindedSpanCommitment) :
    ¬ D.WidePreimageFloor (Dregg2.Crypto.CostAdversary.IsPolyTime D.preAnsSize) :=
  D.widePreimageFloor_polyTime_false

/-- **⚑⚑⚑ THE RE-GROUNDING, IN ONE STATEMENT.** Both halves at once:

  1. the deployed-shape wide blinded span commitment HIDES ITS SPAN — advantage at most
     `(2·Q(λ)+1)/2^λ`, negligible — against EVERY `Q`-query keyed adversary, PROVED
     (information-theoretic, keyed ROM, no assumption);
  2. the floor it replaces — Lane B's `WidePreimageFloor` at `IsPolyTime` — is REFUTED at every
     deployed commitment (Lane B's own theorem, re-exported).

The old conditional hiding statement rested on a false floor; the new one rests on counting. The
one named residual is the ROM-modeling of the wide Poseidon2 (standard, named, not discharged
here). -/
theorem spanHiding_regrounded (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => 2 * (Q l : ℝ) + 1)) :
    HidingHard blindedSpanRomFamily (KeyedRomHidingEff blindedSpanRomFamily Q)
      ∧ ∀ D : Metatheory.Open.BlindedSpanHiding.BlindedSpanCommitment,
          ¬ D.WidePreimageFloor (Dregg2.Crypto.CostAdversary.IsPolyTime D.preAnsSize) :=
  ⟨blindedSpanRom_hiding_negl Q hQ, fun D => D.widePreimageFloor_polyTime_false⟩

/-! ## Kernel-clean keystones. -/

#assert_all_clean [
  condProb_gate_split,
  untouched_filter_card_eq,
  condProb_pin_untouched,
  condProb_pin_diff_le,
  sum_touch_le,
  winProb_challenge_split,
  winProb_pin_dev,
  acceptProb_dev_le,
  hidingAdv_le,
  hidingAdv_le',
  hidingAdv_mem_unit,
  zeroQuery_hidingAdv_eq_zero,
  topAdv_acceptProb_false,
  topAdv_acceptProb_true,
  topAdv_hidingAdv,
  oneQueryAdv_queryHiding,
  oneQueryAdv_acceptProb_false,
  oneQueryAdv_acceptProb_true,
  oneQueryAdv_hidingAdv,
  oneQueryAdv_hidingAdv_pos,
  canary_top_breaks_bound,
  canary_topAdv_not_oneQuery,
  keyedRomHiding_hard,
  hidingTop_false,
  blindedSpanRom_card_B,
  blindedSpanRom_hiding_bound,
  blindedSpanRom_hiding_negl,
  blindedSpanRom_top_false,
  blindedSpanRom_inhabited,
  laneB_polyTime_floor_refuted,
  spanHiding_regrounded
]

end Dregg2.Crypto.KeyedRomHidingFloor

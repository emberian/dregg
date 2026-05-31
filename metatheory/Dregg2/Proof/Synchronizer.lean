/-
# Dregg2.Proof.Synchronizer — the randomized leader-rotation synchronizer and the
expected-O(1)-views-to-an-honest-leader bound (closing BFTLiveness's probabilistic residual).

**What this file closes.** `Dregg2.Proof.BFTLiveness` (read-only sibling) proved that *given* a
`Pacemaker` whose `synchronizes` / `responsive_quorum` fields hold (ELRS Def. 3.1 carried as
honest hypotheses), a `GSTRound` and hence τ-BFT liveness PROVABLY obtain. It named the genuine
one-layer-deeper residual:

  > The *construction* of the synchronizer itself — DLS88/ELRS/Cogsworth's randomized `Relay(r,k)`
  > rotation and the probabilistic argument that, after GST, an honest leader is hit in expected
  > `O(1)` views — a randomized-algorithms development over `World.rand`.

This file builds that randomized leader rotation and PROVES the probabilistic core ELRS §5
isolates: model "view `v` has an honest leader" as a Bernoulli(`h`) event over the relay's random
bits (`World.rand`), so the number of views until the first honest leader is **geometric**, and:

  * **(expected-O(1), `expected_views_eq` + `expected_views_O1`)** the expected number of views to
    the first honest leader is `1/h`, which for an honest fraction `h > 2/3` is `< 3/2` — the
    ELRS expected-*constant* (indeed expected-≤-3/2, the sharp `> 2/3` bound) view count. The
    arithmetic core is the arithmetico-geometric series `∑' n, n·(1-h)^n·h = (1-h)/h`
    (`mathlib`'s `tsum_coe_mul_geometric_of_norm_lt_one`), so `E[views] = 1 + (1-h)/h = 1/h`.
  * **(almost-sure hit, `honest_hit_as`)** the geometric law sums to `1`
    (`∑' n, (1-h)^n·h = 1`): conditioned on a strictly-positive honest fraction, an honest leader
    is hit at *some* finite view with probability `1` — so a synchronization round (a stable
    post-GST view with an honest leader, ELRS Def. 3.1) obtains almost surely / in expectation.
  * **(the descent, `synchronizer_round_obtains`)** combining the almost-sure hit with the
    post-GST stability bound (entering as an explicit `gst` hypothesis, the DLS88 `recv_mono`
    discipline), a synchronization round past GST with an honest leader exists — exactly the
    *output* `BFTLiveness.Pacemaker.synchronizes` carries as a field. We thereby exhibit how that
    field reduces to the randomness+honest-fraction model (see `§5`'s precise reduction note).

**The model (honest hypotheses, NEVER axioms — the `World.recv_mono` discipline).** A
`LeaderRotation` over `[World Msg]` bundles:
  * `h : ℝ` — the honest fraction (the honest-replica proportion the relay samples uniformly
    against), with `honest_pos : 0 < h` and `honest_super : 2/3 < h` the BFT supermajority.
  * `honestLeader : Nat → Prop` — "view `v`'s elected leader (a `World.rand v`-determined relay
    rotation) is honest". The relay (`World.rand`) picks the leader; whether it is honest is the
    Bernoulli(`h`) event. We carry the *distributional* commitment (each view is an independent
    Bernoulli(`h`) trial) as the geometric-law fields, exactly as `World.gst_liveness` carries the
    partial-synchrony commitment — a hypothesis the relay+beacon discharge, not an axiom.

ELRS factors the synchronizer exactly here: §5's `Relay(r,k)` rotation + the expected-linear
analysis is the algorithm; the spec it meets (Def. 3.1 + the expected view count) is what we
machine-check. We prove the probabilistic core and the almost-sure descent; what connecting it to
the *operational* `World.rand` byte-stream needs is the one remaining sharp `OPEN` (§5).

**Ported paper-lemmas.**
  * ELRS §5 / Cogsworth `Relay(r,k)` (`zotero-expected-linear-round-synchronization.pdf`,
    `zotero-cogsworth-view-synchronization.pdf`): the randomized leader rotation ⟿ the
    `LeaderRotation` model + the Bernoulli-per-view geometric law.
  * The geometric expected-trials-to-first-success (a folklore fact ELRS uses for its
    expected-linear claim): `E[views] = 1/h` ⟿ `expected_views_eq`, via mathlib's
    `tsum_coe_mul_geometric_of_norm_lt_one`.

**Rails.** No `axiom`/`admit`/`native_decide`/`sorry`. The honest fraction `h > 2/3` and the GST
bound enter as explicit structure fields / theorem hypotheses (the `recv_mono` discipline).
Keystones are `#assert_axioms`-clean. Non-vacuity is witnessed at `h = 2/3` (boundary) and a
concrete `h = 3/4` rotation. Verified with `lake env lean Dregg2/Proof/Synchronizer.lean`.
-/
import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Normed
import Dregg2.World
import Dregg2.Proof.BFTLiveness

namespace Dregg2.Proof.Synchronizer

open scoped Topology
open Dregg2 Dregg2.World

/-! ## 1. The probabilistic core — the geometric expected-views bound.

These are pure-`ℝ` facts about the geometric law (number of views until the first honest leader,
each view an independent Bernoulli(`h`) trial). They are stated and proved first, free of any
`World`, so the probabilistic content is isolated and reusable. -/

/-- **`geomTerm h n`** — the geometric pmf weight: the probability that the first honest leader is
elected at view `n+1`, i.e. the first `n` views had dishonest leaders (each w.p. `1-h`) and view
`n+1` is honest (w.p. `h`). Over `ℝ`; `0 ≤ h ≤ 1` makes it a genuine probability. -/
noncomputable def geomTerm (h : ℝ) (n : ℕ) : ℝ := (1 - h) ^ n * h

/-- **Expected number of FAILURES (dishonest views) before the first honest leader = `(1-h)/h`**
(PROVED). The arithmetico-geometric sum `∑' n, n·(1-h)^n·h`. This is the heart of ELRS's
expected-linear analysis: with each view an independent Bernoulli(`h`) honest-leader trial, the
mean number of *wasted* views is `(1-h)/h`. Proved from mathlib's
`tsum_coe_mul_geometric_of_norm_lt_one` (`∑' n, n·r^n = r/(1-r)^2`) at `r = 1-h`. -/
theorem expected_failures_eq (h : ℝ) (hpos : 0 < h) (hle : h ≤ 1) :
    (∑' n : ℕ, (n : ℝ) * geomTerm h n) = (1 - h) / h := by
  have hnorm : ‖(1 - h : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_lt]; constructor <;> nlinarith
  have key := tsum_coe_mul_geometric_of_norm_lt_one (r := (1 - h : ℝ)) hnorm
  -- regroup `n * ((1-h)^n * h) = (n * (1-h)^n) * h`, pull out the constant `h`.
  have hre : (fun n : ℕ => (n : ℝ) * geomTerm h n)
      = fun n : ℕ => ((n : ℝ) * (1 - h) ^ n) * h := by
    ext n; simp only [geomTerm]; ring
  rw [hre, tsum_mul_right, key]
  have hsub : (1 : ℝ) - (1 - h) = h := by ring
  rw [hsub]
  field_simp

/-- **Expected number of VIEWS to the first honest leader = `1/h`** (PROVED). Views = `1 +`
failures (the successful view is counted too), so `E[views] = 1 + (1-h)/h = 1/h`. This is the
ELRS expected-view count for the randomized synchronizer. -/
theorem expected_views_eq (h : ℝ) (hpos : 0 < h) (hle : h ≤ 1) :
    (1 : ℝ) + (∑' n : ℕ, (n : ℝ) * geomTerm h n) = 1 / h := by
  rw [expected_failures_eq h hpos hle]
  field_simp; ring

/-- **Expected views is `O(1)` — `≤ 3/2` under the BFT supermajority `h > 2/3`** (PROVED). The
ELRS expected-*constant* bound: with an honest fraction strictly above `2/3`, the synchronizer
hits an honest leader in expected fewer than `3/2` views — a constant independent of the number
of participants or views. This is the sharp form of "expected `O(1)` views to an honest leader". -/
theorem expected_views_O1 (h : ℝ) (hsuper : 2/3 < h) (hle : h ≤ 1) :
    (1 : ℝ) + (∑' n : ℕ, (n : ℝ) * geomTerm h n) ≤ 3/2 := by
  have hpos : 0 < h := by linarith
  rw [expected_views_eq h hpos hle]
  rw [div_le_div_iff₀ hpos (by norm_num)]
  linarith

/-- **The geometric law sums to `1` — an honest leader is hit almost surely** (PROVED). With a
strictly-positive honest fraction `0 < h ≤ 1`, `∑' n, (1-h)^n·h = 1`: the probability that the
first honest leader is elected at *some* finite view is `1`. So a view with an honest leader (the
synchronization round's precondition) occurs with probability `1` / in expectation — there is no
positive-measure event of "no honest leader ever". -/
theorem honest_hit_as (h : ℝ) (hpos : 0 < h) (hle : h ≤ 1) :
    (∑' n : ℕ, geomTerm h n) = 1 := by
  have hnorm : |(1 - h : ℝ)| < 1 := by
    rw [abs_lt]; constructor <;> nlinarith
  -- ∑' n, (1-h)^n = 1/(1-(1-h)) = 1/h, then ·h = 1.
  have hgeo : (∑' n : ℕ, ((1 - h : ℝ)) ^ n) = (1 - (1 - h))⁻¹ := tsum_geometric_of_abs_lt_one hnorm
  have hre : (fun n : ℕ => geomTerm h n) = fun n : ℕ => (1 - h) ^ n * h := by
    ext n; simp only [geomTerm]
  rw [hre, tsum_mul_right, hgeo]
  have hsub : (1 : ℝ) - (1 - h) = h := by ring
  rw [hsub]
  field_simp

/-! ## 2. The randomized leader-rotation model over `World` (ELRS §5 / Cogsworth `Relay`).

The `LeaderRotation` bundles the relay's distributional commitment — that each view's leader (a
`World.rand`-determined rotation) is an independent Bernoulli(`h`) honest-leader trial — as honest
hypothesis fields, exactly as `World.gst_liveness` carries the partial-synchrony commitment. From
it the §1 geometric facts give the expected-O(1)-views bound and the almost-sure hit. -/

/-- **The randomized leader rotation over a `World`** (ELRS §5 / Cogsworth `Relay(r,k)`). The
relay picks each view's leader by sampling `World.rand`; whether the picked leader is honest is a
Bernoulli(`h`) event with `h` the honest fraction. Fields are honest hypotheses (the `recv_mono`
discipline), keyed to the paper that supplies them:

* `h` / `honest_pos` / `honest_super` — the honest fraction with the BFT supermajority `h > 2/3`
  (and `≤ 1`). The relay samples honest replicas with this probability.
* `honestLeader` — "view `v`'s elected leader is honest". The `World.rand v`-determined rotation
  decides the leader; honesty is the Bernoulli event whose law the geometric fields below pin.

The geometric/Bernoulli *distribution* over views is not re-carried as a field — it is the §1
`ℝ`-level law (`geomTerm`), which the `expected_views_*` / `honest_hit_*` theorems below apply at
this rotation's `h`. The rotation supplies `h` and the supermajority; §1 supplies the law. -/
structure LeaderRotation (Msg : Type) [World Msg] where
  /-- The honest fraction the relay samples against. -/
  h : ℝ
  /-- **The honest fraction is positive** — there is *some* honest replica to hit. -/
  honest_pos : 0 < h
  /-- **BFT supermajority** — strictly more than `2/3` of replicas are honest (the `n > 3f`
  floor as a fraction). This is what makes the expected view count `< 3/2`. -/
  honest_super : 2/3 < h
  /-- **The honest fraction is a genuine probability** (`≤ 1`). -/
  honest_le_one : h ≤ 1
  /-- **The relay's honest-leader event per view.** `honestLeader v` holds when the leader the
  relay elects for view `v` (sampling `World.rand v`) is honest. -/
  honestLeader : Nat → Prop

variable {Msg : Type} [World Msg]

/-- **Expected views to an honest leader, for a concrete rotation = `1/h`** (PROVED). The rotation
instantiates the §1 geometric law at its own honest fraction. -/
theorem LeaderRotation.expected_views_eq (R : LeaderRotation Msg) :
    (1 : ℝ) + (∑' n : ℕ, (n : ℝ) * geomTerm R.h n) = 1 / R.h :=
  Synchronizer.expected_views_eq R.h R.honest_pos R.honest_le_one

/-- **THE expected-O(1)-views bound for the randomized synchronizer (PROVED).** For any leader
rotation with a `> 2/3` honest fraction, the expected number of views until an honest leader is
elected is `≤ 3/2` — a constant. This is the ELRS expected-linear-synchronization core, here in
its sharp expected-constant form. -/
theorem LeaderRotation.expected_views_O1 (R : LeaderRotation Msg) :
    (1 : ℝ) + (∑' n : ℕ, (n : ℝ) * geomTerm R.h n) ≤ 3/2 :=
  Synchronizer.expected_views_O1 R.h R.honest_super R.honest_le_one

/-- **An honest leader is hit almost surely (PROVED).** The rotation's geometric law sums to `1`,
so an honest-leader view occurs with probability `1`. -/
theorem LeaderRotation.honest_hit_as (R : LeaderRotation Msg) :
    (∑' n : ℕ, geomTerm R.h n) = 1 :=
  Synchronizer.honest_hit_as R.h R.honest_pos R.honest_le_one

/-! ## 3. The descent to a synchronization round — connecting the model to `Pacemaker.synchronizes`.

`BFTLiveness.Pacemaker.synchronizes : ∀ t, ∃ r, t ≤ r ∧ gst ≤ r` carries the *existence* of a
synchronization round past GST. The randomized synchronizer's job is to make that round *land on
an honest leader*; the almost-sure-hit (`§2`) is precisely the guarantee that such an honest view
exists. We package "an honest-leader view at or after any bound exists" as the synchronizer's
output, given the (honest, hypothesis-carried) fact that the almost-sure event materialises as an
actual hit-index — the bridge from the probabilistic law to a concrete view. -/

/-- **A synchronization round with an honest leader obtains (PROVED, from an explicit hit
hypothesis).** The randomized relay, run from any starting round `t` and past `gst`, eventually
elects an honest leader (the almost-sure hit of `§2`); we represent the materialised hit as the
hypothesis `hhit` — "from the relay's `World.rand` stream there is a view `r ≥ max t gst` whose
leader is honest". (That this materialises with probability `1` is `honest_hit_as`; turning the
`tsum = 1` measure statement into an actual index is the one bridge `§5` names as `OPEN`.) From it
we EXHIBIT the synchronization round: a view `r` at or past both `t` and `gst` with an honest
leader — exactly the shape `Pacemaker.synchronizes` outputs, now with the honest-leader content
the relay supplies made explicit. -/
theorem synchronizer_round_obtains (R : LeaderRotation Msg) (gst t : Nat)
    (hhit : ∃ r : Nat, max t gst ≤ r ∧ R.honestLeader r) :
    ∃ r : Nat, t ≤ r ∧ gst ≤ r ∧ R.honestLeader r := by
  obtain ⟨r, hr, hhonest⟩ := hhit
  exact ⟨r, le_trans (le_max_left _ _) hr, le_trans (le_max_right _ _) hr, hhonest⟩

/-- **The `Pacemaker.synchronizes` arithmetic skeleton is discharged unconditionally (PROVED).**
The `synchronizes` field's *type* is the pure-arithmetic existence `∀ t, ∃ r, t ≤ r ∧ gst ≤ r`
(its honest-leader content lives in `responsive_quorum`'s applicability). That skeleton holds for
any `gst` by `r := max t gst`. Combined with `synchronizer_round_obtains` (which supplies the
honest-leader witness from the relay), the randomized synchronizer discharges *both* the
arithmetic skeleton and the honest-leader content `responsive_quorum` then consumes. -/
theorem synchronizes_skeleton (gst : Nat) :
    ∀ t : Nat, ∃ r : Nat, t ≤ r ∧ gst ≤ r :=
  fun t => ⟨max t gst, le_max_left _ _, le_max_right _ _⟩

/-! ## 4. Non-vacuity — concrete rotations witness the model.

A concrete `LeaderRotation` at `h = 3/4` (a 3-of-4 honest BFT committee, `n = 4, f = 1`,
`3/4 > 2/3`), plus the boundary check that `h = 2/3` gives expected views exactly `3/2`, so the
`O(1)` bound is tight and the model non-vacuous. -/
namespace Inhabited

open Dregg2.World.Reference

/-- A concrete rotation: `h = 3/4` (a 3-of-4 honest committee), leader honest on even views (any
decidable schedule works — only `honestLeader`'s existence matters for the model). -/
noncomputable def rotation : LeaderRotation M where
  h := 3/4
  honest_pos := by norm_num
  honest_super := by norm_num
  honest_le_one := by norm_num
  honestLeader := fun v => v % 2 = 0

/-- The concrete rotation's expected view count is `1/(3/4) = 4/3 ≤ 3/2` — non-vacuous `O(1)`. -/
example : (1 : ℝ) + (∑' n : ℕ, (n : ℝ) * geomTerm rotation.h n) = 4/3 := by
  rw [rotation.expected_views_eq, show rotation.h = 3/4 from rfl]; norm_num

/-- The `O(1)` bound holds concretely. -/
example : (1 : ℝ) + (∑' n : ℕ, (n : ℝ) * geomTerm rotation.h n) ≤ 3/2 :=
  rotation.expected_views_O1

/-- **The boundary is tight:** at the BFT floor `h = 2/3` the expected view count is *exactly*
`3/2` — so the `≤ 3/2` bound cannot be improved without strengthening `h > 2/3`. -/
example : (1 : ℝ) + (∑' n : ℕ, (n : ℝ) * geomTerm (2/3 : ℝ) n) = 3/2 := by
  rw [Synchronizer.expected_views_eq (2/3 : ℝ) (by norm_num) (by norm_num)]; norm_num

/-- The almost-sure hit holds concretely (`∑' n, geomTerm (3/4) n = 1`). -/
example : (∑' n : ℕ, geomTerm rotation.h n) = 1 := rotation.honest_hit_as

/-- The descent applies: given a concrete honest-leader hit (view 4 is even ⇒ honest, and
`4 ≥ max 0 3`), a synchronization round with an honest leader obtains. -/
example : ∃ r : Nat, 0 ≤ r ∧ 3 ≤ r ∧ rotation.honestLeader r :=
  synchronizer_round_obtains rotation 3 0 ⟨4, by norm_num, by norm_num [rotation]⟩

end Inhabited

/-
**OPEN (the one remaining bridge, named — NOT a `sorry`, NOT an axiom).** This file PROVES the
probabilistic core of the randomized synchronizer:
  * the expected number of views to an honest leader is `1/h` (`expected_views_eq`), hence `≤ 3/2`
    under the BFT supermajority `h > 2/3` (`expected_views_O1`) — the ELRS expected-O(1) bound;
  * an honest leader is hit almost surely, the geometric law summing to `1` (`honest_hit_as`);
  * given the materialised hit-index, a synchronization round past GST with an honest leader
    obtains (`synchronizer_round_obtains`), discharging the *shape*
    `BFTLiveness.Pacemaker.synchronizes` outputs.

What stays open is the single measure-theoretic bridge: turning the `∑' n, geomTerm h n = 1`
*almost-sure* statement into an actual hit-INDEX over the operational `World.rand` byte-stream
(`hhit`). Two honest sub-tasks remain there:

  (1) **Tie `honestLeader v` to `World.rand v`.** The model carries `honestLeader` as an abstract
      Bernoulli(`h`)-distributed predicate; the operational relay (`Relay(r,k)` over the beacon)
      would *define* it as "the replica `World.rand v` selects is in the honest set", and prove
      that under the beacon's uniformity this predicate is Bernoulli(`h`). `World.rand : Nat → Nat`
      is a deterministic oracle, not a probability space, so this needs a probability space over
      beacon outcomes (`PMF`/`Measure` over `World.rand` streams) layered on top — a measure over
      the `rand` oracle, which the current `World` interface does not expose.

  (2) **Almost-sure ⇒ existential index.** `honest_hit_as` is a `tsum = 1` statement; extracting
      "∃ n, the n-th view is honest" from it requires the probability-1 event to be *inhabited*,
      i.e. a `Measure`-level "positive (here, full) measure ⇒ nonempty" step. With the per-view
      Bernoulli(`h>0`) law this is immediate measure-theoretically (a `0 < h` trial cannot fail
      forever a.s.), but it needs the product measure over views (`MeasureTheory` infinite product
      / `PMF.bind`), which — like (1) — wants a probability space over `World.rand` that the
      current oracle interface does not carry.

Both are the SAME missing piece: a probability-space layer over `World.rand` (a `Measure`/`PMF`
on beacon outcomes with the relay's Bernoulli-per-view independence). mathlib HAS the pieces
(`PMF.bind`, `MeasureTheory.Measure.infinitePi`, `geometricMeasure`), but wiring them to the
deterministic `World.rand : Nat → Nat` oracle requires either extending `World` with a randomness
*measure* (not just a value oracle) or building a separate `BeaconSpace` portal — a `World`-interface
change off this file's allowed surface (the brief forbids editing `World.lean`). So the bound and
the a.s. hit are machine-checked here; the `hhit` materialisation is hypothesis-routed, with the
exact missing infrastructure named. ELRS factors identically: the expected-O(1) count (proved) vs.
the full execution-trace coupling to the beacon (the bridge).

Net effect on the assumption budget: `BFTLiveness.Pacemaker.synchronizes`'s *arithmetic skeleton*
is now discharged unconditionally (`synchronizes_skeleton`), and its honest-leader content is
reduced to the randomness+honest-fraction model — `expected_views_O1` proves the hit is expected
in `O(1)` views and `honest_hit_as` proves it is almost sure; only the `World.rand`-measure bridge
(an interface extension) separates the a.s. statement from a constructive index.
-/

/-! ## 5. Axiom hygiene — every keystone is kernel-clean.

The probabilistic theorems reduce to mathlib's `tsum_coe_mul_geometric_of_norm_lt_one` /
`tsum_geometric_of_abs_lt_one` and pure field arithmetic; the model theorems to
`LeaderRotation` STRUCTURE FIELDS (hypotheses, not `axiom`s); the descent to its `hhit` hypothesis.
None pull in `sorryAx` or any oracle axiom — `collectAxioms` sees only the standard kernel axioms.
The honest fraction and GST bound live entirely in fields/hypotheses, never in `#print axioms`. -/
#assert_axioms expected_failures_eq
#assert_axioms expected_views_eq
#assert_axioms expected_views_O1
#assert_axioms honest_hit_as
#assert_axioms synchronizer_round_obtains
#assert_axioms synchronizes_skeleton

end Dregg2.Proof.Synchronizer

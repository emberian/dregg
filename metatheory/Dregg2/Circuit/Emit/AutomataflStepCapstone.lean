/-
# Dregg2.Circuit.Emit.AutomataflStepCapstone — LEG A, the n-GENERIC ray fuel induction and the
board-decode / four-ray landing interface the `n = 11` step capstone stands on.

## Why this file exists (and where it sits)

`AutomataflStepRefine` closed the automaton-step refinement at the FROZEN `NN = 2` board: its four
`raycast_*_of_sat` are two-step finite scans (`raycastFuel` unfolded twice, `size = 2` hardcoded) and
its `astep_sat_imp_automatonStep` is stated over the `n = 2` `boardDecode`. `AutomataflCoord` then
supplied the `n`-generic coordinate/one-hot FOUNDATION (`oneHotN_of_sat`, `coordN_of_sat`,
`dot_oneHot(2)`, the `evalH` bridge) and imports `AutomataflStepRefine`. So the Leg-A capstone for the
deployed `n = 11` board CANNOT live in `AutomataflStepRefine` (that would be an import cycle through
`AutomataflCoord`); it lives HERE, downstream of `AutomataflCoord`.

## What this file LANDS (proven, non-vacuous, no `sorry`/`native_decide`/assumed hypothesis)

  * **§1 — THE RAY FUEL INDUCTION.** The `n = 2` scans do not scale: the `n = 11` ray is up to eleven
    steps long, so the reference `Board.raycast` reduction must be an INDUCTION on the step index, not
    a fixed unfolding. `raycastFuel_scan` fast-forwards `m` consecutive in-bounds vacuum steps
    (induction on `m` via the one-step peel `raycastFuel_succ_vac`); `raycast_at_hit` composes it into
    the whole-scan collapse to the single read at the hit step `K`. n-GENERIC — one proof for every
    board size and every cardinal direction.

  * **§2 — `boardDecodeN` + `raycast_of_hit`.** The `n`-generic step board decode, and the single
    four-ray landing lemma: for ANY `Dir` and size `n`, `Board.raycast (boardDecodeN n e) auto d`
    collapses through `raycast_at_hit` to `{ cell-or-wall, K }` given the strictly-before facts. This
    is the ready target each `raycast_*_of_sat` calls once its circuit extraction supplies `K` and the
    before-facts.

## What this file LANDS (continued)

  * **§3–§7 — THE RAY WIRING PLUMBING (∀ n).** `evalHStep_ibEqHead` / `evalHStep_rcReadHead` turn the
    `bif`-guarded window `filterMap` and the `bif`-guarded NESTED gated-read fold into TOTAL
    `List.range n` sums the one-hot collapse can eat; `oneHot_window_sum` is the window-predicate
    indicator; `foldl_step_terms` + `headIsZero_false_of_mem` discharge the `beforeConstraints`
    "this occlusion head is actually emitted" side condition at symbolic `n` (it was a `decide` at
    `n = 2`); `window_{xp,xn,yp,yn}` compute each cardinal's window prefix sum.

  * **§5 — `rayN_of_sat` (∀ n, ALL FOUR RAYS).** The direction-INDEPENDENT extraction: the hit bits
    are a genuine one-hot at a step `K ∈ [1, n]`, the `dist` column IS `K`, every step strictly
    before `K` is in-bounds with a VACUUM read (the occlusion gates), `what` is the `K`-th gated
    read, and `oob_hit` / `cond_nonzero` split it — `ib_K = 1 ⇒ what ≠ 0`, `ib_K = 0 ⇒ what = 0`.

  * **§6 — `ibN_of_sat` / `rcN_of_sat` (∀ n).** The two direction-CARRYING reads: the in-bounds bit
    IS its window prefix sum, and the gated read IS the shifted cell (the doubly-guarded
    `row × col × cell` sum collapsing at the auto one-hot), `0` off the board.

  * **§8 — `raycast_{xp,xn,yp,yn}_of_satN` — ALL FOUR RAYS AT ARBITRARY `n`.** Each cardinal's
    witnessed `(rDist, rWhat)` IS `Board.raycast (boardDecodeN n e) auto dir`. No board size frozen.

  * **§9 — non-vacuity**: the rays instantiate at `n = 3` and the deployed `n = 11`, and the window
    collapse is a two-sided discriminator (in-bounds ⇒ `1`, off-board ⇒ `0`).

## What this file does NOT land — the PRECISE residual

`decideAxis` / `chooseOffset` / `automatonOffset_of_sat` / `astep_sat_imp_automatonStep` are NOT
here at any `n > 2`, and are NOT asserted. The blocker is structural, not incidental: those proofs
live in `AutomataflStepRefine` against the FROZEN `n = 2` descriptor at ABSOLUTE column literals
(`58`/`105`/`152`/`209`), and their gate membership is `by decide` over the concrete 418-constraint
list. `AutomataflStepEmit.NGen` already makes the back-end bases functions of `n`
(`A_DECIDE_X_BASE n` etc.), but `AutomataflStepRefine` §2.5 supplies `n`-generic membership ONLY for
the FRONT end (board range · coordinate decompose · auto one-hots · auto pin · the four rays) —
the Stage-1b back-end and the commitment family are explicitly still `decide`-at-`n = 2`. So
`decideAxis`/`chooseOffset` at symbolic `n` needs (a) an `n`-generic back-end membership layer and
(b) the ~2000-line `forced_ge0` / score / decision-decode chain restated over `A_*_BASE n` rather
than the literals. Neither is done here. The Leg-A capstone is NOT restated at any `n` its proof
cannot reach.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.AutomataflCoord
import Dregg2.Circuit.Emit.AutomataflStepCoord

namespace Dregg2.Circuit.Emit.AutomataflStepCapstone

open Dregg2.Games.Automatafl (Board Coord Particle Dir raycastFuel Raycast)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Circuit.Emit.AutomataflStepRefine (codeToParticle)
open Dregg2.Circuit.Emit.AutomataflStepEmit.NGen (AX AY old)

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## §1 — THE RAY FUEL INDUCTION (pure, n-generic).

The `n = 2` `raycast_*_of_sat` lemmas reduced the reference `Board.raycast` by hand as a two-step
finite scan (`raycastFuel` unfolded twice, `size = 2` hardcoded). At `n = 11` the ray is up to eleven
steps long, so the scan must be an INDUCTION on the step index, not a fixed unfolding.

`raycastFuel_succ_vac` peels one in-bounds vacuum step; `raycastFuel_scan` fast-forwards `m`
consecutive in-bounds vacuum steps (induction on `m`); `raycast_at_hit` combines them: given the ray
is vacuum+in-bounds strictly before step `K`, the whole scan collapses to the single read at step `K`.
This is the pure semantic engine every ray-of-sat lemma calls at ANY board size. -/

/-- Peel one in-bounds vacuum step off a `raycastFuel` scan. -/
theorem raycastFuel_succ_vac (b : Board) (x y dx dy : Int) (dist f : Nat)
    (hin : 0 ≤ x + dx ∧ x + dx < (b.size : Int) ∧ 0 ≤ y + dy ∧ y + dy < (b.size : Int))
    (hvac : (b.cellAt ⟨(x + dx).toNat, (y + dy).toNat⟩).isVacuum = true) :
    raycastFuel b x y dx dy dist (f + 1)
      = raycastFuel b (x + dx) (y + dy) dx dy (dist + 1) f := by
  rw [raycastFuel]
  rw [if_pos hin, if_pos hvac]

/-- Fast-forward `m` consecutive in-bounds vacuum steps of a `raycastFuel` scan (induction on `m`). -/
theorem raycastFuel_scan (b : Board) (dx dy : Int) :
    ∀ (m : Nat) (x y : Int) (dist fuel : Nat), m ≤ fuel →
      (∀ j, 1 ≤ j → j ≤ m →
        (0 ≤ x + (j : Int) * dx ∧ x + (j : Int) * dx < (b.size : Int)
          ∧ 0 ≤ y + (j : Int) * dy ∧ y + (j : Int) * dy < (b.size : Int))
        ∧ (b.cellAt ⟨(x + (j : Int) * dx).toNat, (y + (j : Int) * dy).toNat⟩).isVacuum = true) →
      raycastFuel b x y dx dy dist fuel
        = raycastFuel b (x + (m : Int) * dx) (y + (m : Int) * dy) dx dy (dist + m) (fuel - m) := by
  intro m
  induction m with
  | zero =>
    intro x y dist fuel _ _
    simp
  | succ k ih =>
    intro x y dist fuel hfuel hbefore
    -- fuel = f + 1
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    -- peel step 1
    have hstep1 := hbefore 1 (le_refl 1) (by omega)
    rw [show ((1 : Nat) : Int) * dx = dx by push_cast; ring] at hstep1
    rw [show ((1 : Nat) : Int) * dy = dy by push_cast; ring] at hstep1
    obtain ⟨hin1, hvac1⟩ := hstep1
    rw [raycastFuel_succ_vac b x y dx dy dist f hin1 hvac1]
    -- apply IH at the shifted point
    have hshift := ih (x + dx) (y + dy) (dist + 1) f (by omega)
      (fun j hj1 hjk => by
        rw [show x + dx + (j : Int) * dx = x + ((j + 1 : Nat) : Int) * dx by push_cast; ring]
        rw [show y + dy + (j : Int) * dy = y + ((j + 1 : Nat) : Int) * dy by push_cast; ring]
        exact hbefore (j + 1) (by omega) (by omega))
    rw [hshift]
    -- reconcile the shifted target with the (k+1)-step target
    congr 1
    · push_cast; ring
    · push_cast; ring
    · omega
    · omega

/-- **THE HIT LEMMA — the ray fuel induction, packaged.** If the ray is in-bounds and vacuum at
every step strictly before `K` (`1 ≤ K ≤ fuel`), the whole scan from `(x, y)` collapses to the single
read at step `K`: the `K`-th cell if in bounds, else the wall-vacuum sentinel — both at distance `K`.
This is the semantic target each `raycast_*_of_sat` matches its witnessed `(dist, what)` against. -/
theorem raycast_at_hit (b : Board) (x y dx dy : Int) (K fuel : Nat)
    (hK : 1 ≤ K) (hKf : K ≤ fuel)
    (hbefore : ∀ j, 1 ≤ j → j < K →
      (0 ≤ x + (j : Int) * dx ∧ x + (j : Int) * dx < (b.size : Int)
        ∧ 0 ≤ y + (j : Int) * dy ∧ y + (j : Int) * dy < (b.size : Int))
      ∧ (b.cellAt ⟨(x + (j : Int) * dx).toNat, (y + (j : Int) * dy).toNat⟩).isVacuum = true) :
    raycastFuel b x y dx dy 0 fuel
      = if (0 ≤ x + (K : Int) * dx ∧ x + (K : Int) * dx < (b.size : Int)
            ∧ 0 ≤ y + (K : Int) * dy ∧ y + (K : Int) * dy < (b.size : Int))
        then (if (b.cellAt ⟨(x + (K : Int) * dx).toNat, (y + (K : Int) * dy).toNat⟩).isVacuum
              then raycastFuel b (x + (K : Int) * dx) (y + (K : Int) * dy) dx dy K (fuel - K)
              else { what := b.cellAt ⟨(x + (K : Int) * dx).toNat, (y + (K : Int) * dy).toNat⟩,
                     dist := K })
        else { what := .vacuum, dist := K } := by
  -- scan K-1 vacuum steps
  rw [raycastFuel_scan b dx dy (K - 1) x y 0 fuel (by omega)
        (fun j hj1 hjm => hbefore j hj1 (by omega))]
  -- one more step off the fast-forwarded scan
  have hfuel : fuel - (K - 1) = (fuel - K) + 1 := by omega
  rw [hfuel, raycastFuel]
  -- reconcile x + (K-1)dx + dx = x + K dx, and 0 + (K-1) + 1 = K
  have exK : x + ((K - 1 : Nat) : Int) * dx + dx = x + (K : Int) * dx := by
    have : ((K - 1 : Nat) : Int) = (K : Int) - 1 := by
      rw [Nat.cast_sub hK]; simp
    rw [this]; ring
  have eyK : y + ((K - 1 : Nat) : Int) * dy + dy = y + (K : Int) * dy := by
    have : ((K - 1 : Nat) : Int) = (K : Int) - 1 := by
      rw [Nat.cast_sub hK]; simp
    rw [this]; ring
  have edK : 0 + (K - 1) + 1 = K := by omega
  rw [exK, eyK, edK]

/-! ## §2 — The n-generic step board decode + the four-ray landing interface.

`boardDecodeN` reads a satisfying row of `automataflStepDescN n` back into the reference `Board` at
size `n` (the `n`-generic twin of `AutomataflStepRefine.boardDecode`, which froze `NN = 2`).
`raycast_of_hit` is the SINGLE landing lemma every ray-of-sat proof calls: it unfolds the reference
`Board.raycast` onto the `raycastFuel` scan and discharges it through `raycast_at_hit` — one statement
covering all four cardinal directions at any board size. What a per-ray circuit extraction must still
supply to CALL it is the hit index `K` and the strictly-before in-bounds/vacuum facts (the residual
wiring; see §3). -/

/-- Decode a satisfying `automataflStepDescN n` row's OLD-board columns into the reference `Board` at
size `n`: the auto at `(AX n, AY n)`, cell `(x,y)` the felt-decode of `old[y·n+x]`. -/
def boardDecodeN (n : Nat) (e : VmRowEnv) : Board where
  size          := n
  automaton     := ⟨(e.loc (AX n)).toNat, (e.loc (AY n)).toNat⟩
  cells         := fun c => codeToParticle (e.loc (old n (c.y * n + c.x)))
  useColumnRule := true

@[simp] theorem boardDecodeN_size (n : Nat) (e : VmRowEnv) : (boardDecodeN n e).size = n := rfl

/-- **THE FOUR-RAY LANDING LEMMA.** For ANY cardinal `d` and board size `n`, the reference
`Board.raycast` of the decoded board collapses — via the fuel induction — to the single read at the
hit step `K`, provided the ray is in-bounds and vacuum at every step strictly before `K`
(`1 ≤ K ≤ n`). This is the semantic value each ray's witnessed `(dist, what)` must match; it sits
directly on `raycast_at_hit`, so a ray-of-sat proof reduces to supplying `K` and the before-facts. -/
theorem raycast_of_hit (n : Nat) (e : VmRowEnv) (d : Dir) (K : Nat)
    (hK : 1 ≤ K) (hKn : K ≤ n)
    (hbefore : ∀ j, 1 ≤ j → j < K →
      (0 ≤ ((boardDecodeN n e).automaton.x : Int) + (j : Int) * d.delta.1
        ∧ ((boardDecodeN n e).automaton.x : Int) + (j : Int) * d.delta.1 < (n : Int)
        ∧ 0 ≤ ((boardDecodeN n e).automaton.y : Int) + (j : Int) * d.delta.2
        ∧ ((boardDecodeN n e).automaton.y : Int) + (j : Int) * d.delta.2 < (n : Int))
      ∧ ((boardDecodeN n e).cellAt
          ⟨(((boardDecodeN n e).automaton.x : Int) + (j : Int) * d.delta.1).toNat,
           (((boardDecodeN n e).automaton.y : Int) + (j : Int) * d.delta.2).toNat⟩).isVacuum
          = true) :
    Board.raycast (boardDecodeN n e) (boardDecodeN n e).automaton d
      = if (0 ≤ ((boardDecodeN n e).automaton.x : Int) + (K : Int) * d.delta.1
            ∧ ((boardDecodeN n e).automaton.x : Int) + (K : Int) * d.delta.1 < (n : Int)
            ∧ 0 ≤ ((boardDecodeN n e).automaton.y : Int) + (K : Int) * d.delta.2
            ∧ ((boardDecodeN n e).automaton.y : Int) + (K : Int) * d.delta.2 < (n : Int))
        then (if ((boardDecodeN n e).cellAt
                    ⟨(((boardDecodeN n e).automaton.x : Int) + (K : Int) * d.delta.1).toNat,
                     (((boardDecodeN n e).automaton.y : Int) + (K : Int) * d.delta.2).toNat⟩).isVacuum
              then raycastFuel (boardDecodeN n e)
                     (((boardDecodeN n e).automaton.x : Int) + (K : Int) * d.delta.1)
                     (((boardDecodeN n e).automaton.y : Int) + (K : Int) * d.delta.2)
                     d.delta.1 d.delta.2 K (n + 1 - K)
              else { what := (boardDecodeN n e).cellAt
                       ⟨(((boardDecodeN n e).automaton.x : Int) + (K : Int) * d.delta.1).toNat,
                        (((boardDecodeN n e).automaton.y : Int) + (K : Int) * d.delta.2).toNat⟩,
                     dist := K })
        else { what := .vacuum, dist := K } := by
  have h := raycast_at_hit (boardDecodeN n e)
    ((boardDecodeN n e).automaton.x : Int) ((boardDecodeN n e).automaton.y : Int)
    d.delta.1 d.delta.2 K (n + 1) hK (by omega) hbefore
  simp only [Board.raycast, boardDecodeN_size] at h ⊢
  exact h

/-! ## §3 — PURE LIST/HEAD PLUMBING for the ray wiring.

The `ibEqHead` window is a `filterMap`-with-`bif` over `List.range n`; the `rcReadHead` gated read is
a `bif`-guarded NESTED fold. Both must be turned into total `List.range n` sums before the one-hot
collapse (`dot_oneHotStep` / `dot_oneHotStep2`) can fire. These are the conversions, `n`-generic. -/

open Dregg2.Circuit.Emit.AutomataflStepEmit
open Dregg2.Circuit.Emit.AutomataflStepCoord
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.Emit.AutomataflOcclusionGeneric (OneHotAt)
open Dregg2.Circuit.Emit.AutomataflCoord (varsVal termVal dot_oneHot dot_oneHot2 oneHot_exists
  sum_bool_bounds)

/-- A `bif`-guarded `filterMap` IS a `filter` followed by a `map`. -/
theorem filterMap_bif_eq (L : List Nat) (P : Nat → Bool) (f : Nat → Nat) :
    L.filterMap (fun t => bif P t then some (f t) else none) = (L.filter P).map f := by
  induction L with
  | nil => rfl
  | cons a L ih =>
      by_cases h : P a = true
      · rw [List.filterMap_cons_some (b := f a) (by simp [h]), List.filter_cons_of_pos h,
          List.map_cons, ih]
      · rw [List.filterMap_cons_none (by simp [h]), List.filter_cons_of_neg h, ih]

/-- A sum over a FILTERED list is the total sum of the `if`-guarded summand. -/
theorem sum_filter_eq_sum_ite (L : List Nat) (P : Nat → Bool) (g : Nat → ℤ) :
    ((L.filter P).map g).sum = (L.map (fun j => if P j = true then g j else 0)).sum := by
  induction L with
  | nil => rfl
  | cons a L ih =>
      by_cases h : P a = true
      · simp [List.filter_cons, h, ih]
      · simp only [Bool.not_eq_true] at h
        simp [List.filter_cons, h, ih]

/-- **The window collapse.** A `bif`-guarded window sum of a ONE-HOT selector family is the indicator
of the window predicate at the hot index. This is what turns `ibEqHead`'s prefix-sum into
`[step in bounds]`. -/
theorem oneHot_window_sum {n a0 : Nat} {sel : Nat → Nat} {val : Nat → ℤ}
    (hv : OneHotAt (fun j => val (sel j)) n a0) (P : Nat → Bool) :
    (((List.range n).filterMap (fun t => bif P t then some (sel t) else none)).map val).sum
      = if P a0 = true then 1 else 0 := by
  rw [filterMap_bif_eq, List.map_map, sum_filter_eq_sum_ite]
  have hcong : ((List.range n).map (fun j => if P j = true then ((val ∘ sel) j) else 0))
      = (List.range n).map (fun j => (fun j => val (sel j)) j * (if P j = true then (1 : ℤ) else 0)) := by
    apply List.map_congr_left; intro j _
    by_cases h : P j = true <;> simp [h, Function.comp]
  rw [hcong, dot_oneHot hv (fun j => if P j = true then (1 : ℤ) else 0)]

/-- The `ibEqHead` semantic value: the in-bounds bit MINUS its window prefix sum. -/
theorem evalHStep_ibEqHead (a : Nat → ℤ) (n d : Nat) (dx dy : ℤ) (kk : Nat) :
    evalHStep (NGen.ibEqHead n d dx dy kk) a
      = a (NGen.rIb n d kk) - ((NGen.inWindowCols n dx dy kk).map a).sum := by
  rw [NGen.ibEqHead, evalHStep_append, evalHStep_scale, evalHStep_lin,
    evalHStep_foldl_addLin, evalHStep_zero]
  ring
/-- `Σ (-f) = -(Σ f)` over a mapped list. -/
theorem sum_map_neg (L : List Nat) (f : Nat → ℤ) :
    (L.map (fun j => -(f j))).sum = -((L.map f).sum) := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- The `rcReadHead` semantic value: the gated read MINUS the doubly-guarded `row × col × cell`
sum, as a TOTAL `List.range n × List.range n` sum of `if`-guarded terms (the `bif`-skipped positions
contribute `0`). -/
theorem evalHStep_rcReadHead (a : Nat → ℤ) (n d : Nat) (dx dy : ℤ) (kk : Nat) :
    evalHStep (NGen.rcReadHead n d dx dy kk) a
      = a (NGen.rRc n d kk)
        - ((List.range n).map (fun (y : Nat) => ((List.range n).map (fun (x : Nat) =>
            if (0 ≤ (y : ℤ) + (kk : ℤ) * dy ∧ (y : ℤ) + (kk : ℤ) * dy < (n : ℤ))
                ∧ (0 ≤ (x : ℤ) + (kk : ℤ) * dx ∧ (x : ℤ) + (kk : ℤ) * dx < (n : ℤ))
              then a (NGen.rIb n d kk) * a (NGen.selRow n y) * a (NGen.selCol n x)
                     * a (NGen.old n (((y : ℤ) + (kk : ℤ) * dy).toNat * n
                                       + ((x : ℤ) + (kk : ℤ) * dx).toNat))
              else 0)).sum)).sum := by
  have key : NGen.rcReadHead n d dx dy kk
      = (List.range n).foldl (fun (h : Head) (y : Nat) =>
          bif decide (0 ≤ (y : ℤ) + (kk : ℤ) * dy ∧ (y : ℤ) + (kk : ℤ) * dy < (n : ℤ)) then
            (List.range n).foldl (fun (h2 : Head) (x : Nat) =>
              bif decide (0 ≤ (x : ℤ) + (kk : ℤ) * dx ∧ (x : ℤ) + (kk : ℤ) * dx < (n : ℤ)) then
                h2.addProd (-1) [NGen.rIb n d kk, NGen.selRow n y, NGen.selCol n x,
                  NGen.old n (((y : ℤ) + (kk : ℤ) * dy).toNat * n
                                + ((x : ℤ) + (kk : ℤ) * dx).toNat)]
              else h2) h
          else h) (Head.lin 1 (NGen.rRc n d kk)) := rfl
  have hinner : ∀ (h : Head) (y : Nat),
      evalHStep ((List.range n).foldl (fun (h2 : Head) (x : Nat) =>
          bif decide (0 ≤ (x : ℤ) + (kk : ℤ) * dx ∧ (x : ℤ) + (kk : ℤ) * dx < (n : ℤ)) then
            h2.addProd (-1) [NGen.rIb n d kk, NGen.selRow n y, NGen.selCol n x,
              NGen.old n (((y : ℤ) + (kk : ℤ) * dy).toNat * n + ((x : ℤ) + (kk : ℤ) * dx).toNat)]
          else h2) h) a
        = evalHStep h a + ((List.range n).map (fun (x : Nat) =>
            if (0 ≤ (x : ℤ) + (kk : ℤ) * dx ∧ (x : ℤ) + (kk : ℤ) * dx < (n : ℤ))
              then -(a (NGen.rIb n d kk) * a (NGen.selRow n y) * a (NGen.selCol n x)
                     * a (NGen.old n (((y : ℤ) + (kk : ℤ) * dy).toNat * n
                                       + ((x : ℤ) + (kk : ℤ) * dx).toNat)))
              else 0)).sum := by
    intro h y
    refine evalHStep_foldl_step a h (List.range n) _ _ ?_
    intro h2 x
    by_cases hx : (0 ≤ (x : ℤ) + (kk : ℤ) * dx ∧ (x : ℤ) + (kk : ℤ) * dx < (n : ℤ))
    · rw [show (decide (0 ≤ (x : ℤ) + (kk : ℤ) * dx ∧ (x : ℤ) + (kk : ℤ) * dx < (n : ℤ))) = true
          from decide_eq_true hx, cond_true, if_pos hx, evalHStep_addProd]
      simp only [varsVal, one_mul, List.foldl_cons, List.foldl_nil]
      ring
    · rw [show (decide (0 ≤ (x : ℤ) + (kk : ℤ) * dx ∧ (x : ℤ) + (kk : ℤ) * dx < (n : ℤ))) = false
          from decide_eq_false hx, cond_false, if_neg hx]
      ring
  rw [key, evalHStep_foldl_step a (Head.lin 1 (NGen.rRc n d kk)) (List.range n) _
      (fun (y : Nat) => -(((List.range n).map (fun (x : Nat) =>
        if (0 ≤ (y : ℤ) + (kk : ℤ) * dy ∧ (y : ℤ) + (kk : ℤ) * dy < (n : ℤ))
            ∧ (0 ≤ (x : ℤ) + (kk : ℤ) * dx ∧ (x : ℤ) + (kk : ℤ) * dx < (n : ℤ))
          then a (NGen.rIb n d kk) * a (NGen.selRow n y) * a (NGen.selCol n x)
                 * a (NGen.old n (((y : ℤ) + (kk : ℤ) * dy).toNat * n
                                   + ((x : ℤ) + (kk : ℤ) * dx).toNat))
          else 0)).sum)) ?_, evalHStep_lin, sum_map_neg]
  · ring
  · intro h y
    beta_reduce
    by_cases hy : (0 ≤ (y : ℤ) + (kk : ℤ) * dy ∧ (y : ℤ) + (kk : ℤ) * dy < (n : ℤ))
    · rw [show (decide (0 ≤ (y : ℤ) + (kk : ℤ) * dy ∧ (y : ℤ) + (kk : ℤ) * dy < (n : ℤ))) = true
          from decide_eq_true hy, cond_true, hinner h y]
      congr 1
      rw [← sum_map_neg]
      apply congrArg
      apply List.map_congr_left; intro x _
      by_cases hx : (0 ≤ (x : ℤ) + (kk : ℤ) * dx ∧ (x : ℤ) + (kk : ℤ) * dx < (n : ℤ))
      · rw [if_pos hx, if_pos ⟨hy, hx⟩]
      · rw [if_neg hx, if_neg (fun hc => hx hc.2), neg_zero]
    · rw [show (decide (0 ≤ (y : ℤ) + (kk : ℤ) * dy ∧ (y : ℤ) + (kk : ℤ) * dy < (n : ℤ))) = false
          from decide_eq_false hy, cond_false]
      have hz : ((List.range n).map (fun (x : Nat) =>
          if (0 ≤ (y : ℤ) + (kk : ℤ) * dy ∧ (y : ℤ) + (kk : ℤ) * dy < (n : ℤ))
              ∧ (0 ≤ (x : ℤ) + (kk : ℤ) * dx ∧ (x : ℤ) + (kk : ℤ) * dx < (n : ℤ))
            then a (NGen.rIb n d kk) * a (NGen.selRow n y) * a (NGen.selCol n x)
                   * a (NGen.old n (((y : ℤ) + (kk : ℤ) * dy).toNat * n
                                     + ((x : ℤ) + (kk : ℤ) * dx).toNat))
            else 0)).sum = 0 := by
        have : ((List.range n).map (fun (x : Nat) =>
            if (0 ≤ (y : ℤ) + (kk : ℤ) * dy ∧ (y : ℤ) + (kk : ℤ) * dy < (n : ℤ))
                ∧ (0 ≤ (x : ℤ) + (kk : ℤ) * dx ∧ (x : ℤ) + (kk : ℤ) * dx < (n : ℤ))
              then a (NGen.rIb n d kk) * a (NGen.selRow n y) * a (NGen.selCol n x)
                     * a (NGen.old n (((y : ℤ) + (kk : ℤ) * dy).toNat * n
                                       + ((x : ℤ) + (kk : ℤ) * dx).toNat))
              else 0)) = (List.range n).map (fun _ => (0 : ℤ)) := by
          apply List.map_congr_left; intro x _
          rw [if_neg (fun hc => hy hc.1)]
        rw [this]; simp
      rw [hz]; ring


/-! ## §4 — HEAD-SHAPE plumbing for the OCCLUSION (`beforeConstraints`) gates.

`beforeConstraints` SKIPS a head that is identically zero (`bif headIsZero …`), so the `before_vac`/
`before_inb` membership lemmas carry a `headIsZero … = false` side condition. At `n = 2` that was a
`decide`; at symbolic `n` it must be derived from the fold's TERM LIST. -/

/-- The term list of a `foldl` whose every step APPENDS a fixed block of terms. -/
theorem foldl_step_terms (step : Head → Nat → Head) (g : Nat → List (ℤ × List Nat))
    (hstep : ∀ h j, (step h j).terms = h.terms ++ g j) :
    ∀ (js : List Nat) (init : Head), (js.foldl step init).terms = init.terms ++ js.flatMap g := by
  intro js
  induction js with
  | nil => intro init; simp
  | cons j js ih =>
      intro init
      rw [List.foldl_cons, ih, hstep, List.flatMap_cons, List.append_assoc]

/-- A head carrying ANY nonzero-coefficient term is not `headIsZero` — so it IS emitted. -/
theorem headIsZero_false_of_mem {h : Head} {tm : ℤ × List Nat} (ht : tm ∈ h.terms) (h0 : tm.1 ≠ 0) :
    headIsZero h = false := by
  have hne : ¬ ((h.terms.filter (fun t => t.1 != 0)).isEmpty = true) := by
    intro he
    have hmem : tm ∈ h.terms.filter (fun t => t.1 != 0) :=
      List.mem_filter.mpr ⟨ht, by simpa using h0⟩
    rw [List.isEmpty_iff] at he
    rw [he] at hmem
    exact absurd hmem (List.not_mem_nil)
  simp only [headIsZero, Bool.and_eq_false_iff]
  left
  simpa using hne

/-- `List.range' s n` is `List.range n` shifted — the bridge from the ray's step indexing (`1..n`)
to the `List.range n` the one-hot machinery speaks. -/
theorem range'_eq_map_range : ∀ (n s : Nat), List.range' s n = (List.range n).map (fun j => s + j) := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ k ih =>
      intro s
      rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.range'_succ, ih (s + 1)]
      simp only [Nat.add_zero]
      congr 1
      apply List.map_congr_left; intro j _
      simp only [Function.comp_apply]
      omega

/-- Sum over the ray's step range `1..n` as a sum over `List.range n` at shifted index. -/
theorem sum_range'_one (n : Nat) (f : Nat → ℤ) :
    ((List.range' 1 n).map f).sum = ((List.range n).map (fun j => f (j + 1))).sum := by
  rw [range'_eq_map_range n 1, List.map_map]
  congr 1
  apply List.map_congr_left; intro j _
  simp only [Function.comp]
  congr 1
  omega

/-! ## §5 — THE RAY WIRING, PART A: the DIRECTION-INDEPENDENT extraction (∀ n).

Everything a ray's `(dist, what)` needs from the circuit EXCEPT the two direction-carrying reads
(`ibEqHead`'s window, `rcReadHead`'s shifted cell): the hit one-hot pins a single step `K ∈ [1, n]`,
the distance column IS `K`, the occlusion gates force every strictly-earlier step to be in-bounds
with a VACUUM read, `what` is the `K`-th gated read, and the `oob_hit` / `cond_nonzero` pair splits
on `ib_K`. One proof for all four rays at every board size. -/

/-- The `hib = Σ hit·ib` head, symbolically in `n` (the `rWhat` twin on the in-bounds bits). -/
theorem evalHStep_rayHib (a : Nat → ℤ) (n d : Nat) :
    evalHStep ((List.range' 1 n).foldl
        (fun h (kk : Nat) => h.addProd 1 [NGen.rHit n d kk, NGen.rIb n d kk])
        (Head.lin (-1) (NGen.rHib n d))) a
      = -a (NGen.rHib n d)
        + ((List.range' 1 n).map (fun kk => a (NGen.rHit n d kk) * a (NGen.rIb n d kk))).sum := by
  rw [evalHStep_foldl_step a (Head.lin (-1) (NGen.rHib n d)) (List.range' 1 n) _
      (fun kk => a (NGen.rHit n d kk) * a (NGen.rIb n d kk))
      (by intro h kk; rw [evalHStep_addProd]
          simp only [varsVal, one_mul, List.foldl_cons, List.foldl_nil]),
    evalHStep_lin]
  ring

section RayN
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

open Dregg2.Circuit.Emit.AutomataflStepRefine
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gate_modEq_iff)

/-- **`rayN_of_sat` — the ∀-n, all-directions ray extraction.** On a satisfying canonical trace the
`d`-th ray block witnesses a genuine hit step `K`, its strictly-earlier steps are in-bounds vacuum,
and `what` is the `K`-th gated read, non-vacuum exactly when the hit is in bounds. -/
theorem rayN_of_sat (n d : Nat) (dx dy : ℤ) (hn : (n : ℤ) < 2013265921)
    (hmem : ∀ x, x ∈ NGen.rayConstraints n d dx dy → x ∈ (automataflStepDescN n).constraints)
    (hsat : Satisfied2 hash (automataflStepDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ∃ K : Nat, 1 ≤ K ∧ K ≤ n
      ∧ (envAt t i).loc (NGen.rDist n d) = (K : ℤ)
      ∧ (∀ m, 1 ≤ m → m < K →
          (envAt t i).loc (NGen.rIb n d m) = 1 ∧ (envAt t i).loc (NGen.rRc n d m) = 0)
      ∧ (envAt t i).loc (NGen.rWhat n d) = (envAt t i).loc (NGen.rRc n d K)
      ∧ ((envAt t i).loc (NGen.rIb n d K) = 0 ∨ (envAt t i).loc (NGen.rIb n d K) = 1)
      ∧ ((envAt t i).loc (NGen.rIb n d K) = 1 → (envAt t i).loc (NGen.rWhat n d) ≠ 0)
      ∧ ((envAt t i).loc (NGen.rIb n d K) = 0 → (envAt t i).loc (NGen.rWhat n d) = 0) := by
  set e := envAt t i with he
  -- (a) the hit bits are boolean.
  have hb : ∀ j, j < n → e.loc (NGen.rHit n d (j + 1)) = 0 ∨ e.loc (NGen.rHit n d (j + 1)) = 1 := by
    intro j hj
    exact bin_of_gate (astepN_gate hsat i hi (g := gBin (NGen.rHit n d (j + 1)))
      (hmem _ (ray_hitBit_mem (n := n) (d := d) (dx := dx) (dy := dy) (kk := j + 1)
        (by omega) (by omega)))) (canon_loc hc i _)
  -- (b) the hit bits sum to 1.
  have hsum : ((List.range n).map (fun j => e.loc (NGen.rHit n d (j + 1)))).sum = 1 := by
    have hg := astepN_gate hsat i hi
      (g := headToExpr ((List.range' 1 n).foldl
        (fun h (kk : Nat) => h.addLin 1 (NGen.rHit n d kk)) (Head.c (-1))))
      (hmem _ (ray_sumHit_mem (n := n) (d := d) (dx := dx) (dy := dy)))
    rw [headToExpr_evalStep, evalHStep_rayHitSum,
      sum_range'_one n (fun kk => e.loc (NGen.rHit n d kk))] at hg
    have hmodq : ((List.range n).map (fun j => e.loc (NGen.rHit n d (j + 1)))).sum
        ≡ 1 [ZMOD 2013265921] := (gate_modEq_iff (by ring)).mp hg
    obtain ⟨hlo, hhi⟩ := sum_bool_bounds hb
    exact eq_of_modEq_canon ⟨hlo, lt_of_le_of_lt hhi hn⟩ canon_one hmodq
  -- (c) so the hit bits ARE a one-hot at some step index K = K0 + 1.
  obtain ⟨K0, hone⟩ := oneHot_exists hb hsum
  have hK0n : K0 < n := hone.1
  refine ⟨K0 + 1, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (d) the distance column IS the hit index.
    have hg := astepN_gate hsat i hi
      (g := headToExpr ((List.range' 1 n).foldl
        (fun h (kk : Nat) => h.addLin (kk : ℤ) (NGen.rHit n d kk))
        (Head.lin (-1) (NGen.rDist n d))))
      (hmem _ (ray_dist_mem (n := n) (d := d) (dx := dx) (dy := dy)))
    rw [headToExpr_evalStep, evalHStep_rayDist,
      sum_range'_one n (fun kk => (kk : ℤ) * e.loc (NGen.rHit n d kk))] at hg
    have hT : ((List.range n).map
          (fun j => (((j + 1 : Nat)) : ℤ) * e.loc (NGen.rHit n d (j + 1)))).sum
        = ((K0 + 1 : Nat) : ℤ) := by
      have hcomm : ((List.range n).map
            (fun j => (((j + 1 : Nat)) : ℤ) * e.loc (NGen.rHit n d (j + 1))))
          = (List.range n).map
              (fun j => (fun j => e.loc (NGen.rHit n d (j + 1))) j * ((j : ℤ) + 1)) := by
        apply List.map_congr_left; intro j _; push_cast; ring
      rw [hcomm, dot_oneHot hone (fun j => (j : ℤ) + 1)]; push_cast; ring
    rw [hT] at hg
    exact (eq_of_modEq_canon ⟨by positivity, by push_cast; omega⟩ (canon_loc hc i _)
      ((gate_modEq_iff (by ring)).mp hg)).symm
  · -- (e) the occlusion gates: every step strictly before K is in-bounds with a vacuum read.
    intro m hm1 hmK
    have hii : m - 1 < K0 := by omega
    have hiin : m - 1 < n := by omega
    have hmeq : m - 1 + 1 = m := by omega
    have hK0mem : K0 ∈ (List.range n).filter (fun j => decide (j > m - 1)) :=
      List.mem_filter.mpr ⟨List.mem_range.mpr hK0n, by simpa using hii⟩
    constructor
    · -- in-bounds-before
      have hterms := foldl_step_terms
        (fun h (j : Nat) => (h.addLin 1 (NGen.rHit n d (j + 1))).addProd (-1)
          [NGen.rHit n d (j + 1), NGen.rIb n d (m - 1 + 1)])
        (fun (j : Nat) => [((1 : ℤ), [NGen.rHit n d (j + 1)]),
                           ((-1 : ℤ), [NGen.rHit n d (j + 1), NGen.rIb n d (m - 1 + 1)])])
        (by intro h j; simp [Dregg2.Circuit.GateExpr.GHead.addLin, Dregg2.Circuit.GateExpr.GHead.addProd])
        ((List.range n).filter (fun j => decide (j > m - 1))) Head.zero
      have hnz : headIsZero (((List.range n).filter (fun j => decide (j > m - 1))).foldl
          (fun h (j : Nat) => (h.addLin 1 (NGen.rHit n d (j + 1))).addProd (-1)
            [NGen.rHit n d (j + 1), NGen.rIb n d (m - 1 + 1)]) Head.zero) = false := by
        refine headIsZero_false_of_mem (tm := ((1 : ℤ), [NGen.rHit n d (K0 + 1)])) ?_ (by norm_num)
        rw [hterms]
        refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨K0, hK0mem, ?_⟩)
        exact List.mem_cons.mpr (Or.inl rfl)
      have hg := astepN_gate hsat i hi
        (g := headToExpr (((List.range n).filter (fun j => decide (j > m - 1))).foldl
          (fun h (j : Nat) => (h.addLin 1 (NGen.rHit n d (j + 1))).addProd (-1)
            [NGen.rHit n d (j + 1), NGen.rIb n d (m - 1 + 1)]) Head.zero))
        (hmem _ (ray_before_mem (dx := dx) (dy := dy) (before_inb_mem hiin hnz)))
      rw [headToExpr_evalStep,
        evalHStep_foldl_step e.loc Head.zero
          ((List.range n).filter (fun j => decide (j > m - 1))) _
          (fun j => e.loc (NGen.rHit n d (j + 1))
                     * (1 - e.loc (NGen.rIb n d (m - 1 + 1))))
          (by intro h j
              rw [evalHStep_addProd, evalHStep_addLin]
              simp only [varsVal, one_mul, List.foldl_cons, List.foldl_nil]
              ring),
        evalHStep_zero, sum_filter_eq_sum_ite] at hg
      have hcong : ((List.range n).map (fun j =>
            if (decide (j > m - 1)) = true then
              e.loc (NGen.rHit n d (j + 1)) * (1 - e.loc (NGen.rIb n d (m - 1 + 1))) else 0))
          = (List.range n).map (fun j => (fun j => e.loc (NGen.rHit n d (j + 1))) j
              * (if (decide (j > m - 1)) = true then
                   (1 - e.loc (NGen.rIb n d (m - 1 + 1))) else 0)) := by
        apply List.map_congr_left; intro j _
        by_cases hj : (decide (j > m - 1)) = true <;> simp [hj]
      rw [hcong, dot_oneHot hone
        (fun j => if (decide (j > m - 1)) = true then
                    (1 - e.loc (NGen.rIb n d (m - 1 + 1))) else 0),
        if_pos (by simpa using hii)] at hg
      rw [hmeq] at hg
      exact (eq_of_modEq_canon canon_one (canon_loc hc i _)
        ((gate_modEq_iff (by ring)).mp hg)).symm
    · -- vacuum-before
      have hterms := foldl_step_terms
        (fun h (j : Nat) => h.addProd 1 [NGen.rHit n d (j + 1), NGen.rRc n d (m - 1 + 1)])
        (fun (j : Nat) => [((1 : ℤ), [NGen.rHit n d (j + 1), NGen.rRc n d (m - 1 + 1)])])
        (by intro h j; rfl)
        ((List.range n).filter (fun j => decide (j > m - 1))) Head.zero
      have hnz : headIsZero (((List.range n).filter (fun j => decide (j > m - 1))).foldl
          (fun h (j : Nat) => h.addProd 1 [NGen.rHit n d (j + 1), NGen.rRc n d (m - 1 + 1)])
          Head.zero) = false := by
        refine headIsZero_false_of_mem
          (tm := ((1 : ℤ), [NGen.rHit n d (K0 + 1), NGen.rRc n d (m - 1 + 1)])) ?_ (by norm_num)
        rw [hterms]
        refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨K0, hK0mem, ?_⟩)
        exact List.mem_cons.mpr (Or.inl rfl)
      have hg := astepN_gate hsat i hi
        (g := headToExpr (((List.range n).filter (fun j => decide (j > m - 1))).foldl
          (fun h (j : Nat) => h.addProd 1 [NGen.rHit n d (j + 1), NGen.rRc n d (m - 1 + 1)])
          Head.zero))
        (hmem _ (ray_before_mem (dx := dx) (dy := dy) (before_vac_mem hiin hnz)))
      rw [headToExpr_evalStep,
        evalHStep_foldl_step e.loc Head.zero
          ((List.range n).filter (fun j => decide (j > m - 1))) _
          (fun j => e.loc (NGen.rHit n d (j + 1)) * e.loc (NGen.rRc n d (m - 1 + 1)))
          (by intro h j
              rw [evalHStep_addProd]
              simp only [varsVal, one_mul, List.foldl_cons, List.foldl_nil]),
        evalHStep_zero, sum_filter_eq_sum_ite] at hg
      have hcong : ((List.range n).map (fun j =>
            if (decide (j > m - 1)) = true then
              e.loc (NGen.rHit n d (j + 1)) * e.loc (NGen.rRc n d (m - 1 + 1)) else 0))
          = (List.range n).map (fun j => (fun j => e.loc (NGen.rHit n d (j + 1))) j
              * (if (decide (j > m - 1)) = true then e.loc (NGen.rRc n d (m - 1 + 1)) else 0)) := by
        apply List.map_congr_left; intro j _
        by_cases hj : (decide (j > m - 1)) = true <;> simp [hj]
      rw [hcong, dot_oneHot hone
        (fun j => if (decide (j > m - 1)) = true then e.loc (NGen.rRc n d (m - 1 + 1)) else 0),
        if_pos (by simpa using hii)] at hg
      rw [hmeq] at hg
      exact eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (by ring)).mp hg)
  · -- (f) `what` is the K-th gated read.
    have hg := astepN_gate hsat i hi
      (g := headToExpr ((List.range' 1 n).foldl
        (fun h (kk : Nat) => h.addProd 1 [NGen.rHit n d kk, NGen.rRc n d kk])
        (Head.lin (-1) (NGen.rWhat n d))))
      (hmem _ (ray_whatDot_mem (n := n) (d := d) (dx := dx) (dy := dy)))
    rw [headToExpr_evalStep, evalHStep_rayWhat,
      sum_range'_one n (fun kk => e.loc (NGen.rHit n d kk) * e.loc (NGen.rRc n d kk)),
      dot_oneHot hone (fun j => e.loc (NGen.rRc n d (j + 1)))] at hg
    exact (eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
      ((gate_modEq_iff (by ring)).mp hg)).symm
  · -- (g) the K-th in-bounds bit is boolean.
    exact bin_of_gate (astepN_gate hsat i hi (g := gBin (NGen.rIb n d (K0 + 1)))
      (hmem _ (ray_ibBit_mem (n := n) (d := d) (dx := dx) (dy := dy) (kk := K0 + 1)
        (by omega) (by omega)))) (canon_loc hc i _)
  all_goals {
    -- (h)/(i) the `hib` collapse plus the `oob_hit` / `cond_nonzero` split.
    have hhib : e.loc (NGen.rHib n d) = e.loc (NGen.rIb n d (K0 + 1)) := by
      have hg := astepN_gate hsat i hi
        (g := headToExpr ((List.range' 1 n).foldl
          (fun h (kk : Nat) => h.addProd 1 [NGen.rHit n d kk, NGen.rIb n d kk])
          (Head.lin (-1) (NGen.rHib n d))))
        (hmem _ (ray_hib_mem (n := n) (d := d) (dx := dx) (dy := dy)))
      rw [headToExpr_evalStep, evalHStep_rayHib,
        sum_range'_one n (fun kk => e.loc (NGen.rHit n d kk) * e.loc (NGen.rIb n d kk)),
        dot_oneHot hone (fun j => e.loc (NGen.rIb n d (j + 1)))] at hg
      exact (eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _)
        ((gate_modEq_iff (by ring)).mp hg)).symm
    have hoob := astepN_gate hsat i hi
      (g := headToExpr ((Head.lin 1 (NGen.rWhat n d)).addProd (-1)
        [NGen.rHib n d, NGen.rWhat n d]))
      (hmem _ (ray_oobHit_mem (n := n) (d := d) (dx := dx) (dy := dy)))
    rw [headToExpr_evalStep, evalHStep_addProd, evalHStep_lin] at hoob
    simp only [varsVal, one_mul, List.foldl_cons, List.foldl_nil] at hoob
    have hcond := astepN_gate hsat i hi
      (g := .mul (.var (NGen.rHib n d))
        (.add (.mul (.var (NGen.rWhat n d)) (.var (NGen.rInv n d))) (.const (-1))))
      (hmem _ (ray_cond_mem (n := n) (d := d) (dx := dx) (dy := dy)))
    simp only [EmittedExpr.eval] at hcond
    intro hibK
    rw [hibK] at hhib
    first
    | · -- ib_K = 1 : the read is a genuine non-vacuum particle.
        rw [hhib] at hcond
        intro hw0
        rw [hw0] at hcond
        have : ((1 : ℤ) * (0 * e.loc (NGen.rInv n d) + -1)) = -1 := by ring
        rw [this] at hcond
        obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp hcond
        omega
    | · -- ib_K = 0 : the `oob_hit` gate forces the wall-vacuum code.
        rw [hhib] at hoob
        have hz : (e.loc (NGen.rWhat n d) + -1 * (0 * e.loc (NGen.rWhat n d)))
            = e.loc (NGen.rWhat n d) - 0 := by ring
        rw [hz] at hoob
        exact eq_of_modEq_canon (canon_loc hc i _) canon_zero
          ((gate_modEq_iff (by ring)).mp hoob)
  }

end RayN

/-! ## §6 — THE RAY WIRING, PART B: the two DIRECTION-CARRYING reads (∀ n, all directions).

`ibEqHead` pins the step's in-bounds bit to its window prefix sum; `rcReadHead` pins the step's read
to the SHIFTED cell, gated by that bit. Both collapse through the auto one-hots — and both are
direction-GENERIC once the window sum is supplied (only `inWindowCols` mentions `dx`/`dy`
structurally, and that is computed per-direction in §7). -/

section ReadsN
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

open Dregg2.Circuit.Emit.AutomataflStepRefine
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gate_modEq_iff)

/-- **The in-bounds bit IS its window prefix sum.** -/
theorem ibN_of_sat (n d kk : Nat) (dx dy : ℤ) (b : ℤ)
    (hmem : ∀ x, x ∈ NGen.rayConstraints n d dx dy → x ∈ (automataflStepDescN n).constraints)
    (hsat : Satisfied2 hash (automataflStepDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (h1 : 1 ≤ kk) (h2 : kk ≤ n)
    (hwin : ((NGen.inWindowCols n dx dy kk).map (envAt t i).loc).sum = b) (hbc : Canon b) :
    (envAt t i).loc (NGen.rIb n d kk) = b := by
  have hg := astepN_gate hsat i hi (g := headToExpr (NGen.ibEqHead n d dx dy kk))
    (hmem _ (ray_ibEq_mem (n := n) (d := d) (dx := dx) (dy := dy) (kk := kk) h1 h2))
  rw [headToExpr_evalStep, evalHStep_ibEqHead, hwin] at hg
  exact eq_of_modEq_canon (canon_loc hc i _) hbc ((gate_modEq_iff (by ring)).mp hg)

/-- **The gated read IS the shifted cell.** The doubly-guarded `row × col × cell` sum collapses at
the auto one-hot to the single shifted cell, multiplied by the step's in-bounds bit — and is `0`
when the shifted position leaves the board. Direction-generic. -/
theorem rcN_of_sat (n d kk ax ay : Nat) (dx dy : ℤ)
    (hmem : ∀ x, x ∈ NGen.rayConstraints n d dx dy → x ∈ (automataflStepDescN n).constraints)
    (hsat : Satisfied2 hash (automataflStepDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (h1 : 1 ≤ kk) (h2 : kk ≤ n)
    (hrow : OneHotAt (fun j => (envAt t i).loc (NGen.selRow n j)) n ay)
    (hcol : OneHotAt (fun j => (envAt t i).loc (NGen.selCol n j)) n ax)
    (hib01 : (envAt t i).loc (NGen.rIb n d kk) = 0 ∨ (envAt t i).loc (NGen.rIb n d kk) = 1) :
    (envAt t i).loc (NGen.rRc n d kk)
      = if (0 ≤ (ay : ℤ) + (kk : ℤ) * dy ∧ (ay : ℤ) + (kk : ℤ) * dy < (n : ℤ))
            ∧ (0 ≤ (ax : ℤ) + (kk : ℤ) * dx ∧ (ax : ℤ) + (kk : ℤ) * dx < (n : ℤ))
        then (envAt t i).loc (NGen.rIb n d kk)
               * (envAt t i).loc (NGen.old n (((ay : ℤ) + (kk : ℤ) * dy).toNat * n
                                              + ((ax : ℤ) + (kk : ℤ) * dx).toNat))
        else 0 := by
  set e := envAt t i with he
  have hg := astepN_gate hsat i hi (g := headToExpr (NGen.rcReadHead n d dx dy kk))
    (hmem _ (ray_rcRead_mem (n := n) (d := d) (dx := dx) (dy := dy) (kk := kk) h1 h2))
  rw [headToExpr_evalStep, evalHStep_rcReadHead] at hg
  have hshape : ((List.range n).map (fun (y : Nat) => ((List.range n).map (fun (x : Nat) =>
        if (0 ≤ (y : ℤ) + (kk : ℤ) * dy ∧ (y : ℤ) + (kk : ℤ) * dy < (n : ℤ))
            ∧ (0 ≤ (x : ℤ) + (kk : ℤ) * dx ∧ (x : ℤ) + (kk : ℤ) * dx < (n : ℤ))
          then e.loc (NGen.rIb n d kk) * e.loc (NGen.selRow n y) * e.loc (NGen.selCol n x)
                 * e.loc (NGen.old n (((y : ℤ) + (kk : ℤ) * dy).toNat * n
                                       + ((x : ℤ) + (kk : ℤ) * dx).toNat))
          else 0)).sum)).sum
      = ((List.range n).map (fun (y : Nat) => ((List.range n).map (fun (x : Nat) =>
          (fun j => e.loc (NGen.selRow n j)) y * (fun j => e.loc (NGen.selCol n j)) x
            * (fun (y x : Nat) =>
                if (0 ≤ (y : ℤ) + (kk : ℤ) * dy ∧ (y : ℤ) + (kk : ℤ) * dy < (n : ℤ))
                    ∧ (0 ≤ (x : ℤ) + (kk : ℤ) * dx ∧ (x : ℤ) + (kk : ℤ) * dx < (n : ℤ))
                  then e.loc (NGen.rIb n d kk)
                         * e.loc (NGen.old n (((y : ℤ) + (kk : ℤ) * dy).toNat * n
                                               + ((x : ℤ) + (kk : ℤ) * dx).toNat))
                  else 0) y x)).sum)).sum := by
    apply congrArg
    apply List.map_congr_left; intro y _
    apply congrArg
    apply List.map_congr_left; intro x _
    beta_reduce
    by_cases hcnd : (0 ≤ (y : ℤ) + (kk : ℤ) * dy ∧ (y : ℤ) + (kk : ℤ) * dy < (n : ℤ))
        ∧ (0 ≤ (x : ℤ) + (kk : ℤ) * dx ∧ (x : ℤ) + (kk : ℤ) * dx < (n : ℤ))
    · rw [if_pos hcnd, if_pos hcnd]; ring
    · rw [if_neg hcnd, if_neg hcnd, mul_zero]
  rw [hshape, dot_oneHot2 hrow hcol] at hg
  refine eq_of_modEq_canon (canon_loc hc i _) ?_ ((gate_modEq_iff (by ring)).mp hg)
  by_cases hcnd : (0 ≤ (ay : ℤ) + (kk : ℤ) * dy ∧ (ay : ℤ) + (kk : ℤ) * dy < (n : ℤ))
      ∧ (0 ≤ (ax : ℤ) + (kk : ℤ) * dx ∧ (ax : ℤ) + (kk : ℤ) * dx < (n : ℤ))
  · rw [if_pos hcnd]
    rcases hib01 with h0 | h0
    · rw [h0]; simpa using canon_zero
    · rw [h0, one_mul]; exact canon_loc hc i _
  · rw [if_neg hcnd]; exact canon_zero

end ReadsN

/-! ## §7 — THE FOUR WINDOWS. `inWindowCols` is the ONLY structurally direction-dependent object in
the ray block; here each cardinal's window prefix sum is computed against the auto one-hot. -/

/-- An all-`none` `filterMap` is empty. -/
theorem filterMap_none (L : List Nat) : L.filterMap (fun _ => (none : Option Nat)) = [] := by
  induction L with
  | nil => rfl
  | cons a L ih => rw [List.filterMap_cons_none (h := rfl)]; exact ih

section Windows
variable {v : Nat → ℤ}

/-- **XP window** (`dx = +1`): the in-window columns are `selCol t` for `t ≤ n−1−kk`, so the prefix
sum is `[ax + kk ≤ n − 1]`. -/
theorem window_xp (n kk ax : Nat) (hcol : OneHotAt (fun j => v (NGen.selCol n j)) n ax) :
    ((NGen.inWindowCols n 1 0 kk).map v).sum
      = if (decide ((ax : ℤ) ≤ (n : ℤ) - 1 - (kk : ℤ))) = true then 1 else 0 := by
  rw [NGen.inWindowCols, List.map_append, List.sum_append]
  rw [show ((List.range n).filterMap (fun (t : Nat) =>
        bif ((0 : ℤ) == 1 && decide ((t : ℤ) ≤ (n : ℤ) - 1 - (kk : ℤ)))
            || ((0 : ℤ) == -1 && decide ((t : ℤ) ≥ (kk : ℤ)))
        then some (NGen.selRow n t) else none))
      = (List.range n).filterMap (fun _ => (none : Option Nat)) from rfl, filterMap_none]
  rw [show ((List.range n).filterMap (fun (t : Nat) =>
        bif ((1 : ℤ) == 1 && decide ((t : ℤ) ≤ (n : ℤ) - 1 - (kk : ℤ)))
            || ((1 : ℤ) == -1 && decide ((t : ℤ) ≥ (kk : ℤ)))
        then some (NGen.selCol n t) else none))
      = (List.range n).filterMap (fun (t : Nat) =>
          bif decide ((t : ℤ) ≤ (n : ℤ) - 1 - (kk : ℤ)) then some (NGen.selCol n t) else none) from by
    apply List.filterMap_congr; intro t _
    simp only [show ((1 : ℤ) == 1) = true from rfl, show ((1 : ℤ) == -1) = false from rfl,
      Bool.true_and, Bool.false_and, Bool.or_false]]
  rw [oneHot_window_sum hcol (fun t => decide ((t : ℤ) ≤ (n : ℤ) - 1 - (kk : ℤ)))]
  simp

/-- **XN window** (`dx = −1`): the in-window columns are `selCol t` for `t ≥ kk`, so the prefix sum
is `[ax − kk ≥ 0]`. -/
theorem window_xn (n kk ax : Nat) (hcol : OneHotAt (fun j => v (NGen.selCol n j)) n ax) :
    ((NGen.inWindowCols n (-1) 0 kk).map v).sum
      = if (decide ((ax : ℤ) ≥ (kk : ℤ))) = true then 1 else 0 := by
  rw [NGen.inWindowCols, List.map_append, List.sum_append]
  rw [show ((List.range n).filterMap (fun (t : Nat) =>
        bif ((0 : ℤ) == 1 && decide ((t : ℤ) ≤ (n : ℤ) - 1 - (kk : ℤ)))
            || ((0 : ℤ) == -1 && decide ((t : ℤ) ≥ (kk : ℤ)))
        then some (NGen.selRow n t) else none))
      = (List.range n).filterMap (fun _ => (none : Option Nat)) from rfl, filterMap_none]
  rw [show ((List.range n).filterMap (fun (t : Nat) =>
        bif ((-1 : ℤ) == 1 && decide ((t : ℤ) ≤ (n : ℤ) - 1 - (kk : ℤ)))
            || ((-1 : ℤ) == -1 && decide ((t : ℤ) ≥ (kk : ℤ)))
        then some (NGen.selCol n t) else none))
      = (List.range n).filterMap (fun (t : Nat) =>
          bif decide ((t : ℤ) ≥ (kk : ℤ)) then some (NGen.selCol n t) else none) from by
    apply List.filterMap_congr; intro t _
    simp only [show ((-1 : ℤ) == 1) = false from rfl, show ((-1 : ℤ) == -1) = true from rfl,
      Bool.true_and, Bool.false_and, Bool.false_or]]
  rw [oneHot_window_sum hcol (fun t => decide ((t : ℤ) ≥ (kk : ℤ)))]
  simp

/-- **YP window** (`dy = +1`): the in-window columns are `selRow t` for `t ≤ n−1−kk`. -/
theorem window_yp (n kk ay : Nat) (hrow : OneHotAt (fun j => v (NGen.selRow n j)) n ay) :
    ((NGen.inWindowCols n 0 1 kk).map v).sum
      = if (decide ((ay : ℤ) ≤ (n : ℤ) - 1 - (kk : ℤ))) = true then 1 else 0 := by
  rw [NGen.inWindowCols, List.map_append, List.sum_append]
  rw [show ((List.range n).filterMap (fun (t : Nat) =>
        bif ((0 : ℤ) == 1 && decide ((t : ℤ) ≤ (n : ℤ) - 1 - (kk : ℤ)))
            || ((0 : ℤ) == -1 && decide ((t : ℤ) ≥ (kk : ℤ)))
        then some (NGen.selCol n t) else none))
      = (List.range n).filterMap (fun _ => (none : Option Nat)) from rfl, filterMap_none]
  rw [show ((List.range n).filterMap (fun (t : Nat) =>
        bif ((1 : ℤ) == 1 && decide ((t : ℤ) ≤ (n : ℤ) - 1 - (kk : ℤ)))
            || ((1 : ℤ) == -1 && decide ((t : ℤ) ≥ (kk : ℤ)))
        then some (NGen.selRow n t) else none))
      = (List.range n).filterMap (fun (t : Nat) =>
          bif decide ((t : ℤ) ≤ (n : ℤ) - 1 - (kk : ℤ)) then some (NGen.selRow n t) else none) from by
    apply List.filterMap_congr; intro t _
    simp only [show ((1 : ℤ) == 1) = true from rfl, show ((1 : ℤ) == -1) = false from rfl,
      Bool.true_and, Bool.false_and, Bool.or_false]]
  rw [oneHot_window_sum hrow (fun t => decide ((t : ℤ) ≤ (n : ℤ) - 1 - (kk : ℤ)))]
  simp

/-- **YN window** (`dy = −1`): the in-window columns are `selRow t` for `t ≥ kk`. -/
theorem window_yn (n kk ay : Nat) (hrow : OneHotAt (fun j => v (NGen.selRow n j)) n ay) :
    ((NGen.inWindowCols n 0 (-1) kk).map v).sum
      = if (decide ((ay : ℤ) ≥ (kk : ℤ))) = true then 1 else 0 := by
  rw [NGen.inWindowCols, List.map_append, List.sum_append]
  rw [show ((List.range n).filterMap (fun (t : Nat) =>
        bif ((0 : ℤ) == 1 && decide ((t : ℤ) ≤ (n : ℤ) - 1 - (kk : ℤ)))
            || ((0 : ℤ) == -1 && decide ((t : ℤ) ≥ (kk : ℤ)))
        then some (NGen.selCol n t) else none))
      = (List.range n).filterMap (fun _ => (none : Option Nat)) from rfl, filterMap_none]
  rw [show ((List.range n).filterMap (fun (t : Nat) =>
        bif ((-1 : ℤ) == 1 && decide ((t : ℤ) ≤ (n : ℤ) - 1 - (kk : ℤ)))
            || ((-1 : ℤ) == -1 && decide ((t : ℤ) ≥ (kk : ℤ)))
        then some (NGen.selRow n t) else none))
      = (List.range n).filterMap (fun (t : Nat) =>
          bif decide ((t : ℤ) ≥ (kk : ℤ)) then some (NGen.selRow n t) else none) from by
    apply List.filterMap_congr; intro t _
    simp only [show ((-1 : ℤ) == 1) = false from rfl, show ((-1 : ℤ) == -1) = true from rfl,
      Bool.true_and, Bool.false_and, Bool.false_or]]
  rw [oneHot_window_sum hrow (fun t => decide ((t : ℤ) ≥ (kk : ℤ)))]
  simp

end Windows

/-! ## §8 — THE FOUR RAYS, WIRED AT ARBITRARY `n`.

Each cardinal's witnessed `(dist, what)` IS the reference `Board.raycast` of the decoded board:
the hit one-hot supplies `K`, the occlusion gates supply the strictly-before in-bounds/vacuum facts
`raycast_of_hit` needs, and the `oob_hit` / `cond_nonzero` split matches the reference's
wall-vacuum / first-non-vacuum branches. `∀ n` — no board size is frozen. -/

section Rays
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

open Dregg2.Circuit.Emit.AutomataflStepRefine
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gate_modEq_iff)

/-- **The XP ray, ∀ n.** -/
theorem raycast_xp_of_satN (n : Nat) (hn : (n : ℤ) < 2013265921)
    (hsat : Satisfied2 hash (automataflStepDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    Board.raycast (boardDecodeN n (envAt t i)) (boardDecodeN n (envAt t i)).automaton Dir.xp
      = { what := codeToParticle ((envAt t i).loc (NGen.rWhat n 0)),
          dist := ((envAt t i).loc (NGen.rDist n 0)).toNat } := by
  set e := envAt t i with he
  obtain ⟨ay, hayLt, hayEq, hrow⟩ :=
    oneHotStepN_of_sat hsat hc i hi n hn (NGen.selRow n) (AY n)
      (fun j hj => mem_fe_oneHotRow (oneHot_bool (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))
      (mem_fe_oneHotRow oneHot_sigma) (mem_fe_oneHotRow oneHot_index)
  obtain ⟨ax, haxLt, haxEq, hcol⟩ :=
    oneHotStepN_of_sat hsat hc i hi n hn (NGen.selCol n) (AX n)
      (fun j hj => mem_fe_oneHotCol (oneHot_bool (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))
      (mem_fe_oneHotCol oneHot_sigma) (mem_fe_oneHotCol oneHot_index)
  rw [← he] at hayEq haxEq
  have hmem : ∀ x, x ∈ NGen.rayConstraints n 0 1 0 → x ∈ (automataflStepDescN n).constraints :=
    fun _ hx => mem_fe_ray0 hx
  obtain ⟨K, hK1, hKn, hdist, hbefore, hwhat, hib01, hnz, hz⟩ :=
    rayN_of_sat n 0 1 0 hn hmem hsat hc i hi
  have hMem3 : e.loc (NGen.rWhat n 0) = 0 ∨ e.loc (NGen.rWhat n 0) = 1
      ∨ e.loc (NGen.rWhat n 0) = 2 :=
    mem3_of_gate (astepN_gate hsat i hi (g := memberExpr (NGen.rWhat n 0) [0, 1, 2])
      (hmem _ (ray_whatMem_mem (n := n) (d := 0) (dx := 1) (dy := 0)))) (canon_loc hc i _)
  have hIb : ∀ kk, 1 ≤ kk → kk ≤ n →
      e.loc (NGen.rIb n 0 kk)
        = if (decide ((ax : ℤ) ≤ (n : ℤ) - 1 - (kk : ℤ))) = true then 1 else 0 := by
    intro kk hk1 hk2
    refine ibN_of_sat n 0 kk 1 0 _ hmem hsat hc i hi hk1 hk2 (window_xp n kk ax hcol) ?_
    by_cases hd : (decide ((ax : ℤ) ≤ (n : ℤ) - 1 - (kk : ℤ))) = true
    · rw [if_pos hd]; exact canon_one
    · rw [if_neg hd]; exact canon_zero
  have hRc : ∀ kk, 1 ≤ kk → kk ≤ n →
      e.loc (NGen.rRc n 0 kk)
        = if (0 ≤ (ay : ℤ) + (kk : ℤ) * 0 ∧ (ay : ℤ) + (kk : ℤ) * 0 < (n : ℤ))
              ∧ (0 ≤ (ax : ℤ) + (kk : ℤ) * 1 ∧ (ax : ℤ) + (kk : ℤ) * 1 < (n : ℤ))
          then e.loc (NGen.rIb n 0 kk)
                 * e.loc (NGen.old n (((ay : ℤ) + (kk : ℤ) * 0).toNat * n
                                       + ((ax : ℤ) + (kk : ℤ) * 1).toNat))
          else 0 := by
    intro kk hk1 hk2
    refine rcN_of_sat n 0 kk ax ay 1 0 hmem hsat hc i hi hk1 hk2 hrow hcol ?_
    rw [hIb kk hk1 hk2]
    by_cases hd : (decide ((ax : ℤ) ≤ (n : ℤ) - 1 - (kk : ℤ))) = true
    · rw [if_pos hd]; exact Or.inr rfl
    · rw [if_neg hd]; exact Or.inl rfl
  have hAx : (boardDecodeN n e).automaton.x = ax := by
    show ((e.loc (AX n)).toNat) = ax
    rw [haxEq]; omega
  have hAy : (boardDecodeN n e).automaton.y = ay := by
    show ((e.loc (AY n)).toNat) = ay
    rw [hayEq]; omega
  -- the decoded cell reader, at any in-bounds position.
  have hcellAt : ∀ (X Y : Nat), X < n → Y < n →
      (boardDecodeN n e).cellAt ⟨X, Y⟩ = codeToParticle (e.loc (NGen.old n (Y * n + X))) := by
    intro X Y hX hY
    show (if X < n ∧ Y < n then _ else _) = _
    rw [if_pos ⟨hX, hY⟩]
    rfl
  -- the strictly-before facts.
  have hbeforeRay : ∀ j, 1 ≤ j → j < K →
      (0 ≤ ((boardDecodeN n e).automaton.x : ℤ) + (j : ℤ) * Dir.xp.delta.1
        ∧ ((boardDecodeN n e).automaton.x : ℤ) + (j : ℤ) * Dir.xp.delta.1 < (n : ℤ)
        ∧ 0 ≤ ((boardDecodeN n e).automaton.y : ℤ) + (j : ℤ) * Dir.xp.delta.2
        ∧ ((boardDecodeN n e).automaton.y : ℤ) + (j : ℤ) * Dir.xp.delta.2 < (n : ℤ))
      ∧ ((boardDecodeN n e).cellAt
          ⟨(((boardDecodeN n e).automaton.x : ℤ) + (j : ℤ) * Dir.xp.delta.1).toNat,
           (((boardDecodeN n e).automaton.y : ℤ) + (j : ℤ) * Dir.xp.delta.2).toNat⟩).isVacuum
          = true := by
    intro j hj1 hjK
    rw [hAx, hAy]
    simp only [Dir.delta]
    obtain ⟨hibj, hrcj⟩ := hbefore j hj1 hjK
    have hdj : (ax : ℤ) ≤ (n : ℤ) - 1 - (j : ℤ) := by
      have hv := hIb j hj1 (by omega)
      rw [hibj] at hv
      by_cases hd : (decide ((ax : ℤ) ≤ (n : ℤ) - 1 - (j : ℤ))) = true
      · exact of_decide_eq_true hd
      · rw [if_neg hd] at hv; exact absurd hv.symm (by norm_num)
    have hcondj : (0 ≤ (ay : ℤ) + (j : ℤ) * 0 ∧ (ay : ℤ) + (j : ℤ) * 0 < (n : ℤ))
        ∧ (0 ≤ (ax : ℤ) + (j : ℤ) * 1 ∧ (ax : ℤ) + (j : ℤ) * 1 < (n : ℤ)) := by
      refine ⟨⟨by positivity, by push_cast; omega⟩, ⟨by positivity, by omega⟩⟩
    have hcell0 : e.loc (NGen.old n (ay * n + (ax + j))) = 0 := by
      have hv := hRc j hj1 (by omega)
      rw [if_pos hcondj, hibj, one_mul, hrcj] at hv
      rw [show ((ay : ℤ) + (j : ℤ) * 0).toNat = ay from by omega,
        show ((ax : ℤ) + (j : ℤ) * 1).toNat = ax + j from by omega] at hv
      exact hv.symm
    refine ⟨⟨by positivity, by omega, by positivity, by push_cast; omega⟩, ?_⟩
    rw [show ((ax : ℤ) + (j : ℤ) * 1).toNat = ax + j from by omega,
      show ((ay : ℤ) + (j : ℤ) * 0).toNat = ay from by omega,
      hcellAt (ax + j) ay (by omega) hayLt, hcell0]
    rfl
  rw [raycast_of_hit n e Dir.xp K hK1 (by omega) hbeforeRay, hAx, hAy, hdist]
  rw [show (Dir.xp.delta).1 = (1 : ℤ) from rfl, show (Dir.xp.delta).2 = (0 : ℤ) from rfl]
  rw [show ((K : ℤ)).toNat = K from by omega]
  rcases hib01 with hK0 | hK1v
  · -- the hit is OUT of bounds: the reference reads the wall, the circuit's `what` is forced to 0.
    have hd : ¬ ((ax : ℤ) ≤ (n : ℤ) - 1 - (K : ℤ)) := by
      have hv := hIb K hK1 hKn
      rw [hK0] at hv
      intro hcon
      rw [if_pos (decide_eq_true hcon)] at hv
      exact absurd hv.symm (by norm_num)
    rw [if_neg (by intro hcon; exact hd (by have := hcon.2.1; omega)), hz hK0]
    rfl
  · -- the hit is IN bounds: the reference reads a genuine non-vacuum particle.
    have hd : (ax : ℤ) ≤ (n : ℤ) - 1 - (K : ℤ) := by
      have hv := hIb K hK1 hKn
      rw [hK1v] at hv
      by_cases hcon : (decide ((ax : ℤ) ≤ (n : ℤ) - 1 - (K : ℤ))) = true
      · exact of_decide_eq_true hcon
      · rw [if_neg hcon] at hv; exact absurd hv (by norm_num)
    have hcondK : (0 ≤ (ay : ℤ) + (K : ℤ) * 0 ∧ (ay : ℤ) + (K : ℤ) * 0 < (n : ℤ))
        ∧ (0 ≤ (ax : ℤ) + (K : ℤ) * 1 ∧ (ax : ℤ) + (K : ℤ) * 1 < (n : ℤ)) :=
      ⟨⟨by positivity, by push_cast; omega⟩, ⟨by positivity, by omega⟩⟩
    have hcellK : e.loc (NGen.old n (ay * n + (ax + K))) = e.loc (NGen.rWhat n 0) := by
      have hv := hRc K hK1 hKn
      rw [if_pos hcondK, hK1v, one_mul,
        show ((ay : ℤ) + (K : ℤ) * 0).toNat = ay from by omega,
        show ((ax : ℤ) + (K : ℤ) * 1).toNat = ax + K from by omega] at hv
      rw [hwhat, hv]
    have hwne : e.loc (NGen.rWhat n 0) ≠ 0 := hnz hK1v
    rw [if_pos (⟨by positivity, by omega, by positivity, by push_cast; omega⟩ :
      0 ≤ (ax : ℤ) + (K : ℤ) * 1
        ∧ (ax : ℤ) + (K : ℤ) * 1 < (n : ℤ)
        ∧ 0 ≤ (ay : ℤ) + (K : ℤ) * 0
        ∧ (ay : ℤ) + (K : ℤ) * 0 < (n : ℤ))]
    rw [show ((ax : ℤ) + (K : ℤ) * 1).toNat = ax + K from by omega,
      show ((ay : ℤ) + (K : ℤ) * 0).toNat = ay from by omega,
      hcellAt (ax + K) ay (by omega) hayLt, hcellK]
    rw [if_neg (show ¬ (codeToParticle (e.loc (NGen.rWhat n 0))).isVacuum = true from by
      rcases hMem3 with h | h | h
      · exact absurd h hwne
      · rw [h]; decide
      · rw [h]; decide)]

/-- **The XN ray, ∀ n.** -/
theorem raycast_xn_of_satN (n : Nat) (hn : (n : ℤ) < 2013265921)
    (hsat : Satisfied2 hash (automataflStepDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    Board.raycast (boardDecodeN n (envAt t i)) (boardDecodeN n (envAt t i)).automaton Dir.xn
      = { what := codeToParticle ((envAt t i).loc (NGen.rWhat n 1)),
          dist := ((envAt t i).loc (NGen.rDist n 1)).toNat } := by
  set e := envAt t i with he
  obtain ⟨ay, hayLt, hayEq, hrow⟩ :=
    oneHotStepN_of_sat hsat hc i hi n hn (NGen.selRow n) (AY n)
      (fun j hj => mem_fe_oneHotRow (oneHot_bool (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))
      (mem_fe_oneHotRow oneHot_sigma) (mem_fe_oneHotRow oneHot_index)
  obtain ⟨ax, haxLt, haxEq, hcol⟩ :=
    oneHotStepN_of_sat hsat hc i hi n hn (NGen.selCol n) (AX n)
      (fun j hj => mem_fe_oneHotCol (oneHot_bool (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))
      (mem_fe_oneHotCol oneHot_sigma) (mem_fe_oneHotCol oneHot_index)
  rw [← he] at hayEq haxEq
  have hmem : ∀ x, x ∈ NGen.rayConstraints n 1 (-1) 0 → x ∈ (automataflStepDescN n).constraints :=
    fun _ hx => mem_fe_ray1 hx
  obtain ⟨K, hK1, hKn, hdist, hbefore, hwhat, hib01, hnz, hz⟩ :=
    rayN_of_sat n 1 (-1) 0 hn hmem hsat hc i hi
  have hMem3 : e.loc (NGen.rWhat n 1) = 0 ∨ e.loc (NGen.rWhat n 1) = 1
      ∨ e.loc (NGen.rWhat n 1) = 2 :=
    mem3_of_gate (astepN_gate hsat i hi (g := memberExpr (NGen.rWhat n 1) [0, 1, 2])
      (hmem _ (ray_whatMem_mem (n := n) (d := 1) (dx := -1) (dy := 0)))) (canon_loc hc i _)
  have hIb : ∀ kk, 1 ≤ kk → kk ≤ n →
      e.loc (NGen.rIb n 1 kk) = if (decide ((ax : ℤ) ≥ (kk : ℤ))) = true then 1 else 0 := by
    intro kk hk1 hk2
    refine ibN_of_sat n 1 kk (-1) 0 _ hmem hsat hc i hi hk1 hk2 (window_xn n kk ax hcol) ?_
    by_cases hd : (decide ((ax : ℤ) ≥ (kk : ℤ))) = true
    · rw [if_pos hd]; exact canon_one
    · rw [if_neg hd]; exact canon_zero
  have hRc : ∀ kk, 1 ≤ kk → kk ≤ n →
      e.loc (NGen.rRc n 1 kk)
        = if (0 ≤ (ay : ℤ) + (kk : ℤ) * 0 ∧ (ay : ℤ) + (kk : ℤ) * 0 < (n : ℤ))
              ∧ (0 ≤ (ax : ℤ) + (kk : ℤ) * (-1) ∧ (ax : ℤ) + (kk : ℤ) * (-1) < (n : ℤ))
          then e.loc (NGen.rIb n 1 kk)
                 * e.loc (NGen.old n (((ay : ℤ) + (kk : ℤ) * 0).toNat * n
                                       + ((ax : ℤ) + (kk : ℤ) * (-1)).toNat))
          else 0 := by
    intro kk hk1 hk2
    refine rcN_of_sat n 1 kk ax ay (-1) 0 hmem hsat hc i hi hk1 hk2 hrow hcol ?_
    rw [hIb kk hk1 hk2]
    by_cases hd : (decide ((ax : ℤ) ≥ (kk : ℤ))) = true
    · rw [if_pos hd]; exact Or.inr rfl
    · rw [if_neg hd]; exact Or.inl rfl
  have hAx : (boardDecodeN n e).automaton.x = ax := by
    show ((e.loc (AX n)).toNat) = ax
    rw [haxEq]; omega
  have hAy : (boardDecodeN n e).automaton.y = ay := by
    show ((e.loc (AY n)).toNat) = ay
    rw [hayEq]; omega
  have hcellAt : ∀ (X Y : Nat), X < n → Y < n →
      (boardDecodeN n e).cellAt ⟨X, Y⟩ = codeToParticle (e.loc (NGen.old n (Y * n + X))) := by
    intro X Y hX hY
    show (if X < n ∧ Y < n then _ else _) = _
    rw [if_pos ⟨hX, hY⟩]
    rfl
  have hbeforeRay : ∀ j, 1 ≤ j → j < K →
      (0 ≤ ((boardDecodeN n e).automaton.x : ℤ) + (j : ℤ) * Dir.xn.delta.1
        ∧ ((boardDecodeN n e).automaton.x : ℤ) + (j : ℤ) * Dir.xn.delta.1 < (n : ℤ)
        ∧ 0 ≤ ((boardDecodeN n e).automaton.y : ℤ) + (j : ℤ) * Dir.xn.delta.2
        ∧ ((boardDecodeN n e).automaton.y : ℤ) + (j : ℤ) * Dir.xn.delta.2 < (n : ℤ))
      ∧ ((boardDecodeN n e).cellAt
          ⟨(((boardDecodeN n e).automaton.x : ℤ) + (j : ℤ) * Dir.xn.delta.1).toNat,
           (((boardDecodeN n e).automaton.y : ℤ) + (j : ℤ) * Dir.xn.delta.2).toNat⟩).isVacuum
          = true := by
    intro j hj1 hjK
    rw [hAx, hAy]
    simp only [Dir.delta]
    obtain ⟨hibj, hrcj⟩ := hbefore j hj1 hjK
    have hdj : (ax : ℤ) ≥ (j : ℤ) := by
      have hv := hIb j hj1 (by omega)
      rw [hibj] at hv
      by_cases hd : (decide ((ax : ℤ) ≥ (j : ℤ))) = true
      · exact of_decide_eq_true hd
      · rw [if_neg hd] at hv; exact absurd hv.symm (by norm_num)
    have hcondj : (0 ≤ (ay : ℤ) + (j : ℤ) * 0 ∧ (ay : ℤ) + (j : ℤ) * 0 < (n : ℤ))
        ∧ (0 ≤ (ax : ℤ) + (j : ℤ) * (-1) ∧ (ax : ℤ) + (j : ℤ) * (-1) < (n : ℤ)) := by
      refine ⟨⟨by positivity, by push_cast; omega⟩, ⟨by omega, by omega⟩⟩
    have hcell0 : e.loc (NGen.old n (ay * n + (ax - j))) = 0 := by
      have hv := hRc j hj1 (by omega)
      rw [if_pos hcondj, hibj, one_mul, hrcj] at hv
      rw [show ((ay : ℤ) + (j : ℤ) * 0).toNat = ay from by omega,
        show ((ax : ℤ) + (j : ℤ) * (-1)).toNat = ax - j from by omega] at hv
      exact hv.symm
    refine ⟨⟨by omega, by omega, by positivity, by push_cast; omega⟩, ?_⟩
    rw [show ((ax : ℤ) + (j : ℤ) * (-1)).toNat = ax - j from by omega,
      show ((ay : ℤ) + (j : ℤ) * 0).toNat = ay from by omega,
      hcellAt (ax - j) ay (by omega) hayLt, hcell0]
    rfl
  rw [raycast_of_hit n e Dir.xn K hK1 (by omega) hbeforeRay, hAx, hAy, hdist]
  rw [show (Dir.xn.delta).1 = (-1 : ℤ) from rfl, show (Dir.xn.delta).2 = (0 : ℤ) from rfl]
  rw [show ((K : ℤ)).toNat = K from by omega]
  rcases hib01 with hK0 | hK1v
  · have hd : ¬ ((ax : ℤ) ≥ (K : ℤ)) := by
      have hv := hIb K hK1 hKn
      rw [hK0] at hv
      intro hcon
      rw [if_pos (decide_eq_true hcon)] at hv
      exact absurd hv.symm (by norm_num)
    rw [if_neg (by intro hcon; exact hd (by have := hcon.1; omega)), hz hK0]
    rfl
  · have hd : (ax : ℤ) ≥ (K : ℤ) := by
      have hv := hIb K hK1 hKn
      rw [hK1v] at hv
      by_cases hcon : (decide ((ax : ℤ) ≥ (K : ℤ))) = true
      · exact of_decide_eq_true hcon
      · rw [if_neg hcon] at hv; exact absurd hv (by norm_num)
    have hcondK : (0 ≤ (ay : ℤ) + (K : ℤ) * 0 ∧ (ay : ℤ) + (K : ℤ) * 0 < (n : ℤ))
        ∧ (0 ≤ (ax : ℤ) + (K : ℤ) * (-1) ∧ (ax : ℤ) + (K : ℤ) * (-1) < (n : ℤ)) :=
      ⟨⟨by positivity, by push_cast; omega⟩, ⟨by omega, by omega⟩⟩
    have hcellK : e.loc (NGen.old n (ay * n + (ax - K))) = e.loc (NGen.rWhat n 1) := by
      have hv := hRc K hK1 hKn
      rw [if_pos hcondK, hK1v, one_mul,
        show ((ay : ℤ) + (K : ℤ) * 0).toNat = ay from by omega,
        show ((ax : ℤ) + (K : ℤ) * (-1)).toNat = ax - K from by omega] at hv
      rw [hwhat, hv]
    have hwne : e.loc (NGen.rWhat n 1) ≠ 0 := hnz hK1v
    rw [if_pos (⟨by omega, by omega, by positivity, by push_cast; omega⟩ :
      0 ≤ (ax : ℤ) + (K : ℤ) * (-1)
        ∧ (ax : ℤ) + (K : ℤ) * (-1) < (n : ℤ)
        ∧ 0 ≤ (ay : ℤ) + (K : ℤ) * 0
        ∧ (ay : ℤ) + (K : ℤ) * 0 < (n : ℤ))]
    rw [show ((ax : ℤ) + (K : ℤ) * (-1)).toNat = ax - K from by omega,
      show ((ay : ℤ) + (K : ℤ) * 0).toNat = ay from by omega,
      hcellAt (ax - K) ay (by omega) hayLt, hcellK]
    rw [if_neg (show ¬ (codeToParticle (e.loc (NGen.rWhat n 1))).isVacuum = true from by
      rcases hMem3 with h | h | h
      · exact absurd h hwne
      · rw [h]; decide
      · rw [h]; decide)]

/-- **The YP ray, ∀ n.** -/
theorem raycast_yp_of_satN (n : Nat) (hn : (n : ℤ) < 2013265921)
    (hsat : Satisfied2 hash (automataflStepDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    Board.raycast (boardDecodeN n (envAt t i)) (boardDecodeN n (envAt t i)).automaton Dir.yp
      = { what := codeToParticle ((envAt t i).loc (NGen.rWhat n 2)),
          dist := ((envAt t i).loc (NGen.rDist n 2)).toNat } := by
  set e := envAt t i with he
  obtain ⟨ay, hayLt, hayEq, hrow⟩ :=
    oneHotStepN_of_sat hsat hc i hi n hn (NGen.selRow n) (AY n)
      (fun j hj => mem_fe_oneHotRow (oneHot_bool (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))
      (mem_fe_oneHotRow oneHot_sigma) (mem_fe_oneHotRow oneHot_index)
  obtain ⟨ax, haxLt, haxEq, hcol⟩ :=
    oneHotStepN_of_sat hsat hc i hi n hn (NGen.selCol n) (AX n)
      (fun j hj => mem_fe_oneHotCol (oneHot_bool (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))
      (mem_fe_oneHotCol oneHot_sigma) (mem_fe_oneHotCol oneHot_index)
  rw [← he] at hayEq haxEq
  have hmem : ∀ x, x ∈ NGen.rayConstraints n 2 0 1 → x ∈ (automataflStepDescN n).constraints :=
    fun _ hx => mem_fe_ray2 hx
  obtain ⟨K, hK1, hKn, hdist, hbefore, hwhat, hib01, hnz, hz⟩ :=
    rayN_of_sat n 2 0 1 hn hmem hsat hc i hi
  have hMem3 : e.loc (NGen.rWhat n 2) = 0 ∨ e.loc (NGen.rWhat n 2) = 1
      ∨ e.loc (NGen.rWhat n 2) = 2 :=
    mem3_of_gate (astepN_gate hsat i hi (g := memberExpr (NGen.rWhat n 2) [0, 1, 2])
      (hmem _ (ray_whatMem_mem (n := n) (d := 2) (dx := 0) (dy := 1)))) (canon_loc hc i _)
  have hIb : ∀ kk, 1 ≤ kk → kk ≤ n →
      e.loc (NGen.rIb n 2 kk)
        = if (decide ((ay : ℤ) ≤ (n : ℤ) - 1 - (kk : ℤ))) = true then 1 else 0 := by
    intro kk hk1 hk2
    refine ibN_of_sat n 2 kk 0 1 _ hmem hsat hc i hi hk1 hk2 (window_yp n kk ay hrow) ?_
    by_cases hd : (decide ((ay : ℤ) ≤ (n : ℤ) - 1 - (kk : ℤ))) = true
    · rw [if_pos hd]; exact canon_one
    · rw [if_neg hd]; exact canon_zero
  have hRc : ∀ kk, 1 ≤ kk → kk ≤ n →
      e.loc (NGen.rRc n 2 kk)
        = if (0 ≤ (ay : ℤ) + (kk : ℤ) * 1 ∧ (ay : ℤ) + (kk : ℤ) * 1 < (n : ℤ))
              ∧ (0 ≤ (ax : ℤ) + (kk : ℤ) * 0 ∧ (ax : ℤ) + (kk : ℤ) * 0 < (n : ℤ))
          then e.loc (NGen.rIb n 2 kk)
                 * e.loc (NGen.old n (((ay : ℤ) + (kk : ℤ) * 1).toNat * n
                                       + ((ax : ℤ) + (kk : ℤ) * 0).toNat))
          else 0 := by
    intro kk hk1 hk2
    refine rcN_of_sat n 2 kk ax ay 0 1 hmem hsat hc i hi hk1 hk2 hrow hcol ?_
    rw [hIb kk hk1 hk2]
    by_cases hd : (decide ((ay : ℤ) ≤ (n : ℤ) - 1 - (kk : ℤ))) = true
    · rw [if_pos hd]; exact Or.inr rfl
    · rw [if_neg hd]; exact Or.inl rfl
  have hAx : (boardDecodeN n e).automaton.x = ax := by
    show ((e.loc (AX n)).toNat) = ax
    rw [haxEq]; omega
  have hAy : (boardDecodeN n e).automaton.y = ay := by
    show ((e.loc (AY n)).toNat) = ay
    rw [hayEq]; omega
  have hcellAt : ∀ (X Y : Nat), X < n → Y < n →
      (boardDecodeN n e).cellAt ⟨X, Y⟩ = codeToParticle (e.loc (NGen.old n (Y * n + X))) := by
    intro X Y hX hY
    show (if X < n ∧ Y < n then _ else _) = _
    rw [if_pos ⟨hX, hY⟩]
    rfl
  have hbeforeRay : ∀ j, 1 ≤ j → j < K →
      (0 ≤ ((boardDecodeN n e).automaton.x : ℤ) + (j : ℤ) * Dir.yp.delta.1
        ∧ ((boardDecodeN n e).automaton.x : ℤ) + (j : ℤ) * Dir.yp.delta.1 < (n : ℤ)
        ∧ 0 ≤ ((boardDecodeN n e).automaton.y : ℤ) + (j : ℤ) * Dir.yp.delta.2
        ∧ ((boardDecodeN n e).automaton.y : ℤ) + (j : ℤ) * Dir.yp.delta.2 < (n : ℤ))
      ∧ ((boardDecodeN n e).cellAt
          ⟨(((boardDecodeN n e).automaton.x : ℤ) + (j : ℤ) * Dir.yp.delta.1).toNat,
           (((boardDecodeN n e).automaton.y : ℤ) + (j : ℤ) * Dir.yp.delta.2).toNat⟩).isVacuum
          = true := by
    intro j hj1 hjK
    rw [hAx, hAy]
    simp only [Dir.delta]
    obtain ⟨hibj, hrcj⟩ := hbefore j hj1 hjK
    have hdj : (ay : ℤ) ≤ (n : ℤ) - 1 - (j : ℤ) := by
      have hv := hIb j hj1 (by omega)
      rw [hibj] at hv
      by_cases hd : (decide ((ay : ℤ) ≤ (n : ℤ) - 1 - (j : ℤ))) = true
      · exact of_decide_eq_true hd
      · rw [if_neg hd] at hv; exact absurd hv.symm (by norm_num)
    have hcondj : (0 ≤ (ay : ℤ) + (j : ℤ) * 1 ∧ (ay : ℤ) + (j : ℤ) * 1 < (n : ℤ))
        ∧ (0 ≤ (ax : ℤ) + (j : ℤ) * 0 ∧ (ax : ℤ) + (j : ℤ) * 0 < (n : ℤ)) := by
      refine ⟨⟨by positivity, by omega⟩, ⟨by positivity, by push_cast; omega⟩⟩
    have hcell0 : e.loc (NGen.old n ((ay + j) * n + ax)) = 0 := by
      have hv := hRc j hj1 (by omega)
      rw [if_pos hcondj, hibj, one_mul, hrcj] at hv
      rw [show ((ay : ℤ) + (j : ℤ) * 1).toNat = ay + j from by omega,
        show ((ax : ℤ) + (j : ℤ) * 0).toNat = ax from by omega] at hv
      exact hv.symm
    refine ⟨⟨by positivity, by push_cast; omega, by positivity, by omega⟩, ?_⟩
    rw [show ((ax : ℤ) + (j : ℤ) * 0).toNat = ax from by omega,
      show ((ay : ℤ) + (j : ℤ) * 1).toNat = ay + j from by omega,
      hcellAt ax (ay + j) haxLt (by omega), hcell0]
    rfl
  rw [raycast_of_hit n e Dir.yp K hK1 (by omega) hbeforeRay, hAx, hAy, hdist]
  rw [show (Dir.yp.delta).1 = (0 : ℤ) from rfl, show (Dir.yp.delta).2 = (1 : ℤ) from rfl]
  rw [show ((K : ℤ)).toNat = K from by omega]
  rcases hib01 with hK0 | hK1v
  · have hd : ¬ ((ay : ℤ) ≤ (n : ℤ) - 1 - (K : ℤ)) := by
      have hv := hIb K hK1 hKn
      rw [hK0] at hv
      intro hcon
      rw [if_pos (decide_eq_true hcon)] at hv
      exact absurd hv.symm (by norm_num)
    rw [if_neg (by intro hcon; exact hd (by have := hcon.2.2.2; omega)), hz hK0]
    rfl
  · have hd : (ay : ℤ) ≤ (n : ℤ) - 1 - (K : ℤ) := by
      have hv := hIb K hK1 hKn
      rw [hK1v] at hv
      by_cases hcon : (decide ((ay : ℤ) ≤ (n : ℤ) - 1 - (K : ℤ))) = true
      · exact of_decide_eq_true hcon
      · rw [if_neg hcon] at hv; exact absurd hv (by norm_num)
    have hcondK : (0 ≤ (ay : ℤ) + (K : ℤ) * 1 ∧ (ay : ℤ) + (K : ℤ) * 1 < (n : ℤ))
        ∧ (0 ≤ (ax : ℤ) + (K : ℤ) * 0 ∧ (ax : ℤ) + (K : ℤ) * 0 < (n : ℤ)) :=
      ⟨⟨by positivity, by omega⟩, ⟨by positivity, by push_cast; omega⟩⟩
    have hcellK : e.loc (NGen.old n ((ay + K) * n + ax)) = e.loc (NGen.rWhat n 2) := by
      have hv := hRc K hK1 hKn
      rw [if_pos hcondK, hK1v, one_mul,
        show ((ay : ℤ) + (K : ℤ) * 1).toNat = ay + K from by omega,
        show ((ax : ℤ) + (K : ℤ) * 0).toNat = ax from by omega] at hv
      rw [hwhat, hv]
    have hwne : e.loc (NGen.rWhat n 2) ≠ 0 := hnz hK1v
    rw [if_pos (⟨by positivity, by push_cast; omega, by positivity, by omega⟩ :
      0 ≤ (ax : ℤ) + (K : ℤ) * 0
        ∧ (ax : ℤ) + (K : ℤ) * 0 < (n : ℤ)
        ∧ 0 ≤ (ay : ℤ) + (K : ℤ) * 1
        ∧ (ay : ℤ) + (K : ℤ) * 1 < (n : ℤ))]
    rw [show ((ax : ℤ) + (K : ℤ) * 0).toNat = ax from by omega,
      show ((ay : ℤ) + (K : ℤ) * 1).toNat = ay + K from by omega,
      hcellAt ax (ay + K) haxLt (by omega), hcellK]
    rw [if_neg (show ¬ (codeToParticle (e.loc (NGen.rWhat n 2))).isVacuum = true from by
      rcases hMem3 with h | h | h
      · exact absurd h hwne
      · rw [h]; decide
      · rw [h]; decide)]

/-- **The YN ray, ∀ n.** -/
theorem raycast_yn_of_satN (n : Nat) (hn : (n : ℤ) < 2013265921)
    (hsat : Satisfied2 hash (automataflStepDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    Board.raycast (boardDecodeN n (envAt t i)) (boardDecodeN n (envAt t i)).automaton Dir.yn
      = { what := codeToParticle ((envAt t i).loc (NGen.rWhat n 3)),
          dist := ((envAt t i).loc (NGen.rDist n 3)).toNat } := by
  set e := envAt t i with he
  obtain ⟨ay, hayLt, hayEq, hrow⟩ :=
    oneHotStepN_of_sat hsat hc i hi n hn (NGen.selRow n) (AY n)
      (fun j hj => mem_fe_oneHotRow (oneHot_bool (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))
      (mem_fe_oneHotRow oneHot_sigma) (mem_fe_oneHotRow oneHot_index)
  obtain ⟨ax, haxLt, haxEq, hcol⟩ :=
    oneHotStepN_of_sat hsat hc i hi n hn (NGen.selCol n) (AX n)
      (fun j hj => mem_fe_oneHotCol (oneHot_bool (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))
      (mem_fe_oneHotCol oneHot_sigma) (mem_fe_oneHotCol oneHot_index)
  rw [← he] at hayEq haxEq
  have hmem : ∀ x, x ∈ NGen.rayConstraints n 3 0 (-1) → x ∈ (automataflStepDescN n).constraints :=
    fun _ hx => mem_fe_ray3 hx
  obtain ⟨K, hK1, hKn, hdist, hbefore, hwhat, hib01, hnz, hz⟩ :=
    rayN_of_sat n 3 0 (-1) hn hmem hsat hc i hi
  have hMem3 : e.loc (NGen.rWhat n 3) = 0 ∨ e.loc (NGen.rWhat n 3) = 1
      ∨ e.loc (NGen.rWhat n 3) = 2 :=
    mem3_of_gate (astepN_gate hsat i hi (g := memberExpr (NGen.rWhat n 3) [0, 1, 2])
      (hmem _ (ray_whatMem_mem (n := n) (d := 3) (dx := 0) (dy := -1)))) (canon_loc hc i _)
  have hIb : ∀ kk, 1 ≤ kk → kk ≤ n →
      e.loc (NGen.rIb n 3 kk) = if (decide ((ay : ℤ) ≥ (kk : ℤ))) = true then 1 else 0 := by
    intro kk hk1 hk2
    refine ibN_of_sat n 3 kk 0 (-1) _ hmem hsat hc i hi hk1 hk2 (window_yn n kk ay hrow) ?_
    by_cases hd : (decide ((ay : ℤ) ≥ (kk : ℤ))) = true
    · rw [if_pos hd]; exact canon_one
    · rw [if_neg hd]; exact canon_zero
  have hRc : ∀ kk, 1 ≤ kk → kk ≤ n →
      e.loc (NGen.rRc n 3 kk)
        = if (0 ≤ (ay : ℤ) + (kk : ℤ) * (-1) ∧ (ay : ℤ) + (kk : ℤ) * (-1) < (n : ℤ))
              ∧ (0 ≤ (ax : ℤ) + (kk : ℤ) * 0 ∧ (ax : ℤ) + (kk : ℤ) * 0 < (n : ℤ))
          then e.loc (NGen.rIb n 3 kk)
                 * e.loc (NGen.old n (((ay : ℤ) + (kk : ℤ) * (-1)).toNat * n
                                       + ((ax : ℤ) + (kk : ℤ) * 0).toNat))
          else 0 := by
    intro kk hk1 hk2
    refine rcN_of_sat n 3 kk ax ay 0 (-1) hmem hsat hc i hi hk1 hk2 hrow hcol ?_
    rw [hIb kk hk1 hk2]
    by_cases hd : (decide ((ay : ℤ) ≥ (kk : ℤ))) = true
    · rw [if_pos hd]; exact Or.inr rfl
    · rw [if_neg hd]; exact Or.inl rfl
  have hAx : (boardDecodeN n e).automaton.x = ax := by
    show ((e.loc (AX n)).toNat) = ax
    rw [haxEq]; omega
  have hAy : (boardDecodeN n e).automaton.y = ay := by
    show ((e.loc (AY n)).toNat) = ay
    rw [hayEq]; omega
  have hcellAt : ∀ (X Y : Nat), X < n → Y < n →
      (boardDecodeN n e).cellAt ⟨X, Y⟩ = codeToParticle (e.loc (NGen.old n (Y * n + X))) := by
    intro X Y hX hY
    show (if X < n ∧ Y < n then _ else _) = _
    rw [if_pos ⟨hX, hY⟩]
    rfl
  have hbeforeRay : ∀ j, 1 ≤ j → j < K →
      (0 ≤ ((boardDecodeN n e).automaton.x : ℤ) + (j : ℤ) * Dir.yn.delta.1
        ∧ ((boardDecodeN n e).automaton.x : ℤ) + (j : ℤ) * Dir.yn.delta.1 < (n : ℤ)
        ∧ 0 ≤ ((boardDecodeN n e).automaton.y : ℤ) + (j : ℤ) * Dir.yn.delta.2
        ∧ ((boardDecodeN n e).automaton.y : ℤ) + (j : ℤ) * Dir.yn.delta.2 < (n : ℤ))
      ∧ ((boardDecodeN n e).cellAt
          ⟨(((boardDecodeN n e).automaton.x : ℤ) + (j : ℤ) * Dir.yn.delta.1).toNat,
           (((boardDecodeN n e).automaton.y : ℤ) + (j : ℤ) * Dir.yn.delta.2).toNat⟩).isVacuum
          = true := by
    intro j hj1 hjK
    rw [hAx, hAy]
    simp only [Dir.delta]
    obtain ⟨hibj, hrcj⟩ := hbefore j hj1 hjK
    have hdj : (ay : ℤ) ≥ (j : ℤ) := by
      have hv := hIb j hj1 (by omega)
      rw [hibj] at hv
      by_cases hd : (decide ((ay : ℤ) ≥ (j : ℤ))) = true
      · exact of_decide_eq_true hd
      · rw [if_neg hd] at hv; exact absurd hv.symm (by norm_num)
    have hcondj : (0 ≤ (ay : ℤ) + (j : ℤ) * (-1) ∧ (ay : ℤ) + (j : ℤ) * (-1) < (n : ℤ))
        ∧ (0 ≤ (ax : ℤ) + (j : ℤ) * 0 ∧ (ax : ℤ) + (j : ℤ) * 0 < (n : ℤ)) := by
      refine ⟨⟨by omega, by omega⟩, ⟨by positivity, by push_cast; omega⟩⟩
    have hcell0 : e.loc (NGen.old n ((ay - j) * n + ax)) = 0 := by
      have hv := hRc j hj1 (by omega)
      rw [if_pos hcondj, hibj, one_mul, hrcj] at hv
      rw [show ((ay : ℤ) + (j : ℤ) * (-1)).toNat = ay - j from by omega,
        show ((ax : ℤ) + (j : ℤ) * 0).toNat = ax from by omega] at hv
      exact hv.symm
    refine ⟨⟨by positivity, by push_cast; omega, by omega, by omega⟩, ?_⟩
    rw [show ((ax : ℤ) + (j : ℤ) * 0).toNat = ax from by omega,
      show ((ay : ℤ) + (j : ℤ) * (-1)).toNat = ay - j from by omega,
      hcellAt ax (ay - j) haxLt (by omega), hcell0]
    rfl
  rw [raycast_of_hit n e Dir.yn K hK1 (by omega) hbeforeRay, hAx, hAy, hdist]
  rw [show (Dir.yn.delta).1 = (0 : ℤ) from rfl, show (Dir.yn.delta).2 = (-1 : ℤ) from rfl]
  rw [show ((K : ℤ)).toNat = K from by omega]
  rcases hib01 with hK0 | hK1v
  · have hd : ¬ ((ay : ℤ) ≥ (K : ℤ)) := by
      have hv := hIb K hK1 hKn
      rw [hK0] at hv
      intro hcon
      rw [if_pos (decide_eq_true hcon)] at hv
      exact absurd hv.symm (by norm_num)
    rw [if_neg (by intro hcon; exact hd (by have := hcon.2.2.1; omega)), hz hK0]
    rfl
  · have hd : (ay : ℤ) ≥ (K : ℤ) := by
      have hv := hIb K hK1 hKn
      rw [hK1v] at hv
      by_cases hcon : (decide ((ay : ℤ) ≥ (K : ℤ))) = true
      · exact of_decide_eq_true hcon
      · rw [if_neg hcon] at hv; exact absurd hv (by norm_num)
    have hcondK : (0 ≤ (ay : ℤ) + (K : ℤ) * (-1) ∧ (ay : ℤ) + (K : ℤ) * (-1) < (n : ℤ))
        ∧ (0 ≤ (ax : ℤ) + (K : ℤ) * 0 ∧ (ax : ℤ) + (K : ℤ) * 0 < (n : ℤ)) :=
      ⟨⟨by omega, by omega⟩, ⟨by positivity, by push_cast; omega⟩⟩
    have hcellK : e.loc (NGen.old n ((ay - K) * n + ax)) = e.loc (NGen.rWhat n 3) := by
      have hv := hRc K hK1 hKn
      rw [if_pos hcondK, hK1v, one_mul,
        show ((ay : ℤ) + (K : ℤ) * (-1)).toNat = ay - K from by omega,
        show ((ax : ℤ) + (K : ℤ) * 0).toNat = ax from by omega] at hv
      rw [hwhat, hv]
    have hwne : e.loc (NGen.rWhat n 3) ≠ 0 := hnz hK1v
    rw [if_pos (⟨by positivity, by push_cast; omega, by omega, by omega⟩ :
      0 ≤ (ax : ℤ) + (K : ℤ) * 0
        ∧ (ax : ℤ) + (K : ℤ) * 0 < (n : ℤ)
        ∧ 0 ≤ (ay : ℤ) + (K : ℤ) * (-1)
        ∧ (ay : ℤ) + (K : ℤ) * (-1) < (n : ℤ))]
    rw [show ((ax : ℤ) + (K : ℤ) * 0).toNat = ax from by omega,
      show ((ay : ℤ) + (K : ℤ) * (-1)).toNat = ay - K from by omega,
      hcellAt ax (ay - K) haxLt (by omega), hcellK]
    rw [if_neg (show ¬ (codeToParticle (e.loc (NGen.rWhat n 3))).isVacuum = true from by
      rcases hMem3 with h | h | h
      · exact absurd h hwne
      · rw [h]; decide
      · rw [h]; decide)]

end Rays

/-! ## §9 — NON-VACUITY: the ∀-n rays INSTANTIATE, and the window teeth BITE.

The ray theorems carry exactly one side condition on the board size (`n < p`), so they discharge at
`n = 3` and at the deployed `n = 11`. And the window collapse is a REAL discriminator, not a
tautology: at `n = 3` the same one-hot yields `1` for an in-bounds step and `0` for an out-of-bounds
one — an `rIb` witness of the wrong polarity has no satisfying assignment. -/

section NonVacuity
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

open Dregg2.Circuit.Emit.AutomataflStepRefine (StepCanon)

/-- The four rays at `n = 3`. -/
theorem raycast_xp_n3 (hsat : Satisfied2 hash (automataflStepDescN 3) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    Board.raycast (boardDecodeN 3 (envAt t i)) (boardDecodeN 3 (envAt t i)).automaton Dir.xp
      = { what := codeToParticle ((envAt t i).loc (NGen.rWhat 3 0)),
          dist := ((envAt t i).loc (NGen.rDist 3 0)).toNat } :=
  raycast_xp_of_satN 3 (by norm_num) hsat hc i hi

/-- The XP ray at the deployed `n = 11`. -/
theorem raycast_xp_n11 (hsat : Satisfied2 hash (automataflStepDescN 11) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    Board.raycast (boardDecodeN 11 (envAt t i)) (boardDecodeN 11 (envAt t i)).automaton Dir.xp
      = { what := codeToParticle ((envAt t i).loc (NGen.rWhat 11 0)),
          dist := ((envAt t i).loc (NGen.rDist 11 0)).toNat } :=
  raycast_xp_of_satN 11 (by norm_num) hsat hc i hi

/-- The YN ray at the deployed `n = 11` (the fourth cardinal instantiates too). -/
theorem raycast_yn_n11 (hsat : Satisfied2 hash (automataflStepDescN 11) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    Board.raycast (boardDecodeN 11 (envAt t i)) (boardDecodeN 11 (envAt t i)).automaton Dir.yn
      = { what := codeToParticle ((envAt t i).loc (NGen.rWhat 11 3)),
          dist := ((envAt t i).loc (NGen.rDist 11 3)).toNat } :=
  raycast_yn_of_satN 11 (by norm_num) hsat hc i hi

end NonVacuity

/-- **The XP window BITES (n = 3, auto in column 0).** Step `kk = 2` is in bounds from column 0, so
the emitted prefix sum FORCES `rIb = 1`. -/
theorem window_xp_n3_col0_step2_inbounds :
    ((NGen.inWindowCols 3 1 0 2).map (fun c => if c = NGen.selCol 3 0 then (1 : ℤ) else 0)).sum
      = 1 := by
  rw [window_xp 3 2 0 (v := fun c => if c = NGen.selCol 3 0 then (1 : ℤ) else 0)
    ⟨by norm_num, by intro j hj; interval_cases j <;> simp [NGen.selCol, NGen.KK,
      NGen.COORD_RBITS]⟩]
  norm_num

/-- **…and REFUSES the wrong polarity (n = 3, auto in column 2).** Step `kk = 2` leaves the board
from column 2, so the SAME gate forces `rIb = 0` — a witness claiming `1` has no satisfying
assignment. This is the two-sided canary: the window is a discriminator, not a tautology. -/
theorem window_xp_n3_col2_step2_outofbounds :
    ((NGen.inWindowCols 3 1 0 2).map (fun c => if c = NGen.selCol 3 2 then (1 : ℤ) else 0)).sum
      = 0 := by
  rw [window_xp 3 2 2 (v := fun c => if c = NGen.selCol 3 2 then (1 : ℤ) else 0)
    ⟨by norm_num, by intro j hj; interval_cases j <;> simp [NGen.selCol, NGen.KK,
      NGen.COORD_RBITS]⟩]
  norm_num

/-! ## §10 — Axiom pins. -/

#assert_axioms raycastFuel_succ_vac
#assert_axioms raycastFuel_scan
#assert_axioms raycast_at_hit
#assert_axioms raycast_of_hit
#assert_axioms oneHot_window_sum
#assert_axioms evalHStep_ibEqHead
#assert_axioms evalHStep_rcReadHead
#assert_axioms headIsZero_false_of_mem
#assert_axioms range'_eq_map_range
#assert_axioms rayN_of_sat
#assert_axioms ibN_of_sat
#assert_axioms rcN_of_sat
#assert_axioms window_xp
#assert_axioms window_xn
#assert_axioms window_yp
#assert_axioms window_yn
#assert_axioms raycast_xp_of_satN
#assert_axioms raycast_xn_of_satN
#assert_axioms raycast_yp_of_satN
#assert_axioms raycast_yn_of_satN
#assert_axioms raycast_xp_n3
#assert_axioms raycast_xp_n11
#assert_axioms raycast_yn_n11
#assert_axioms window_xp_n3_col0_step2_inbounds
#assert_axioms window_xp_n3_col2_step2_outofbounds

end Dregg2.Circuit.Emit.AutomataflStepCapstone

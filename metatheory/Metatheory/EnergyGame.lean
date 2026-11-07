/-
# Metatheory.EnergyGame — the GRADED / ENERGY safety game, compiled into the Boolean kernel.

gpt5.5's move: a bounded **graded** safety game need not be solved with new fixed-point machinery —
*compile the bounded grade into the world*. Expand the world to `EWorld := World × Grade`, where
`Grade` is a capped budget-accumulator (`ℕ`, accumulated with the `PolisGrade` max-plus quantale's
`⊗ = +`, capped at the budget). Lift the base game to an `EGame` over `EWorld` whose step ACCUMULATES
the transition cost into the grade and whose floor is `base.floor w ∧ grade ≤ budget`. Then the WHOLE
`SafetyGame` apparatus — `ViabilityKernel`, `kernel_invariant`, `kernel_maximal`, `kernelShield`,
`kernelShield_preserves` — applies UNCHANGED to `EGame`. Nothing new to prove about fixpoints.

The payoffs, all corollaries of the reused kernel:
  * **`ViabilityKernel (EGame …)` IS the graded winning region** — the set of `(w, g)` from which the
    controller can keep `base.floor` AND `grade ≤ budget` forever. (`kernel_subset_floor`,
    `kernel_invariant` specialise to the energy floor.)
  * **`energy_safe`** — the kernel-shield over `EGame` keeps `grade ≤ budget` (and the base floor) for
    EVERY controller, at every tick. The budget is never overrun, no matter what the controller does.
  * **Boolean safety is the `B`-trivial degenerate case** — with cost ≡ 0, the grade never moves off
    `0 ≤ B`, the energy floor collapses to the base floor, and `EGame.ViabilityKernel` projects to the
    base game's. The energy game CONTAINS Boolean safety.
  * **The composed catch as ONE game**: death-by-a-thousand-cuts (many small costs summing past `B`) is
    refused, AND a single big jump (one cost over `B`) is refused — by the *same* energy floor. The two
    failure modes the Boolean composition `combineFloor` had to catch on two axes are now one accumulator.

Reuses `SafetyGame.Game` + kernel machinery on `EWorld` verbatim; the grade arithmetic is the
`PolisGrade` max-plus quantale (`comp = +`, `unit = 0`). No load-bearing `True`;
`#eval`/`#guard`/`example`s assert TRUE props (`decide` tells the truth).
-/
import Metatheory.SafetyGame
import Polis.PolisGrade

namespace Metatheory.EnergyGame

open Metatheory.SafetyGame
open Metatheory.PolisGrade (GradeAlgebra)

universe u

/-! ## §1. The energy world and the cost-bearing lift.

A `CostGame` is a Boolean safety game (`SafetyGame.Game`) together with a per-transition COST and a
`budget`. Cost accumulates with the max-plus quantale's `⊗ = +` on `ℕ` (the `PolisGrade` model:
sequential cost adds). The grade is CAPPED at `budget + 1` so the state space stays finite/bounded —
once you have overspent, the exact overspend is irrelevant (any `g > budget` is out of floor), so we
saturate at the sentinel `budget + 1` ("over budget"). -/

/-- A Boolean safety game enriched with a per-transition cost and a global budget. The grade lives in
`ℕ` and accumulates with `PolisGrade`'s `⊗ = +` (sequential cost). -/
structure CostGame where
  base : Game.{u}
  /-- The cost of a single transition (the `⊗`-increment to the grade). -/
  cost : base.World → base.Move → base.Resp → Nat
  /-- The grade budget: the floor demands `grade ≤ budget`. -/
  budget : Nat

variable (C : CostGame)

/-- The **energy world**: a base world paired with the accumulated grade (spent budget). -/
abbrev EWorld : Type u := C.base.World × Nat

/-- The capped grade accumulation: add the cost (`⊗` of the max-plus quantale), then SATURATE at
`budget + 1` so the grade space is bounded ("over budget" is a single sentinel). Below the budget this
is exactly `g + c`; the `PolisGrade.comp` is the `+`. -/
def bump (g c : Nat) : Nat := min (GradeAlgebra.comp g c) (C.budget + 1)

/-- Below saturation `bump` is literally the quantale `⊗` (`+`): no information lost while in budget. -/
theorem bump_eq_comp {g c : Nat} (h : GradeAlgebra.comp g c ≤ C.budget + 1) :
    bump C g c = GradeAlgebra.comp g c := by
  unfold bump; exact Nat.min_eq_left h

/-- `bump` never lowers the grade (cost is non-negative; saturation only pulls toward the cap, and the
cap is reached only at or above the budget). The accumulator is monotone — you cannot un-spend. -/
theorem le_bump (g c : Nat) (hg : g ≤ C.budget + 1) : g ≤ bump C g c := by
  unfold bump GradeAlgebra.comp
  show g ≤ min (g + c) (C.budget + 1)
  omega

/-! ## §2. The energy game — a `SafetyGame.Game` over `EWorld`.

The whole point: `EGame C` is an ordinary `Game`. Its move/resp are the base's; its step threads the
cost into the grade with `bump`; its floor is the base floor AND `grade ≤ budget`. Everything in
`SafetyGame` then applies to it with NO new machinery. -/

/-- The lifted **energy game**: same moves/responses, step accumulates cost into the grade, floor is
`base.floor w ∧ grade ≤ budget`. A genuine `SafetyGame.Game` over `EWorld`. -/
def EGame : Game.{u} where
  World := EWorld C
  Move := C.base.Move
  Resp := C.base.Resp
  step := fun (w, g) m r => (C.base.step w m r, bump C g (C.cost w m r))
  legal := fun (w, _) m r => C.base.legal w m r
  floor := fun (w, g) => C.base.floor w ∧ g ≤ C.budget

/-- The energy floor, spelled out: base floor AND in budget. -/
theorem egame_floor (w : C.base.World) (g : Nat) :
    (EGame C).floor (w, g) ↔ (C.base.floor w ∧ g ≤ C.budget) := Iff.rfl

/-! ## §3. The graded winning region IS the reused viability kernel.

`ViabilityKernel (EGame C)` — the `SafetyGame` greatest controlled invariant — is BY DEFINITION the
set of `(w, g)` from which the controller can keep `base.floor ∧ grade ≤ budget` forever. We do not
reprove the fixpoint facts; we *specialise* the `SafetyGame` ones to the energy floor. -/

/-- The **graded winning region**: the set of energy states from which the controller can maintain the
base floor and stay in budget indefinitely. This is exactly `SafetyGame.ViabilityKernel (EGame C)`. -/
abbrev GradedWinning : EWorld C → Prop := ViabilityKernel (EGame C)

/-- A graded-winning state is in budget AND satisfies the base floor — the kernel sits inside the
energy floor (`SafetyGame.kernel_subset_floor` specialised). The budget is respected at the kernel. -/
theorem winning_in_budget (p : EWorld C) (h : GradedWinning C p) :
    C.base.floor p.1 ∧ p.2 ≤ C.budget :=
  kernel_subset_floor (EGame C) p h

/-- From a graded-winning state there IS a controllable move keeping you graded-winning against every
legal response — the kernel is a controlled invariant (`SafetyGame.kernel_invariant` specialised). The
controller can always preserve "in budget, floor holds". -/
theorem winning_invariant (w : C.base.World) (g : Nat) (h : GradedWinning C (w, g)) :
    CPre (EGame C) (GradedWinning C) (w, g) :=
  kernel_invariant (EGame C) (w, g) h

/-- The graded winning region is the GREATEST energy-floor-contained controlled invariant: any region
`X` the controller can keep inside the energy floor lies within it (`SafetyGame.kernel_maximal`). No
correct graded governor is more permissive than shielding this region. -/
theorem winning_maximal (X : EWorld C → Prop)
    (hX : ∀ p, X p → (EGame C).floor p ∧ CPre (EGame C) X p) :
    ∀ p, X p → GradedWinning C p :=
  kernel_maximal (EGame C) X hX

/-! ## §4. `energy_safe` — the kernel-shield keeps the budget for EVERY controller.

Reuse `SafetyGame.kernelShield` + `kernelShield_preserves` over `EGame C`. The shielded trajectory
stays graded-winning ⇒ stays in budget ⇒ never overruns, for any opaque controller. -/

/-- A controller's choice of base move at each energy state, paired with the adversary's response
strategy — the inputs `SafetyGame.kernelShield` needs over `EGame C`. -/
abbrev EResp := EWorld C → C.base.Move → C.base.Resp

/-- The shielded energy trajectory: iterate the kernel-shield over `EGame C` under a controller. -/
noncomputable def shieldTraj (resp : EResp C) (ctrl : EWorld C → C.base.Move)
    (p0 : EWorld C) : Nat → EWorld C
  | 0 => p0
  | n + 1 =>
      let p := shieldTraj resp ctrl p0 n
      kernelShield (EGame C) resp p (ctrl p)

/-- One shielded step keeps the graded-winning region — directly `kernelShield_preserves`. -/
theorem shield_step_winning (resp : EResp C) (p : EWorld C) (m : C.base.Move)
    (h : GradedWinning C p) :
    GradedWinning C (kernelShield (EGame C) resp p m) :=
  kernelShield_preserves (EGame C) resp p m h

/-- **`energy_safe`** — under the kernel-shield over `EGame C`, from any graded-winning start, for
EVERY controller and at EVERY tick: the world stays in budget (`grade ≤ budget`) and the base floor
holds. The budget is never overrun, whatever the controller does. The energy analogue of
`SafetyGame.genGov_safe`, obtained for free from the reused kernel. -/
theorem energy_safe (resp : EResp C) (ctrl : EWorld C → C.base.Move) (p0 : EWorld C)
    (h0 : GradedWinning C p0) :
    ∀ n, C.base.floor (shieldTraj C resp ctrl p0 n).1
       ∧ (shieldTraj C resp ctrl p0 n).2 ≤ C.budget := by
  intro n
  have hwin : ∀ k, GradedWinning C (shieldTraj C resp ctrl p0 k) := by
    intro k
    induction k with
    | zero => exact h0
    | succ j ih => exact shield_step_winning C resp _ _ ih
  exact winning_in_budget C _ (hwin n)

/-! ## §5. Boolean safety is the `B`-trivial degenerate case.

With cost ≡ 0, the grade NEVER changes off its start: `bump g 0 = min g (B+1)`, and starting at `g = 0`
keeps `g = 0 ≤ B` forever. The energy floor `base.floor w ∧ 0 ≤ B` collapses to the base floor, so the
energy game's controllable-predecessor and kernel coincide with the base game's (on the `g = 0` slice).
The energy game CONTAINS Boolean safety. -/

/-- The **zero-cost lift** of a base game: cost ≡ 0, any budget. (Budget `0` is the tightest.) -/
def trivialCost (G : Game.{u}) (B : Nat) : CostGame.{u} where
  base := G
  cost := fun _ _ _ => 0
  budget := B

/-- With cost ≡ 0 and starting grade `0`, the grade stays `0` after any zero-cost step. -/
theorem trivial_grade_stays (G : Game.{u}) (B : Nat) (w : G.World) (m : G.Move) (r : G.Resp) :
    ((EGame (trivialCost G B)).step (w, 0) m r).2 = 0 := by
  show bump (trivialCost G B) 0 0 = 0
  unfold bump
  show min (GradeAlgebra.comp (0 : Nat) 0) (B + 1) = 0
  rw [show GradeAlgebra.comp (0 : Nat) 0 = 0 from rfl]
  exact Nat.zero_min _

/-- On the `g = 0` slice, the energy floor is EXACTLY the base floor (budget always met at grade `0`).
So the Boolean game is recovered: the energy floor degenerates to `base.floor`. -/
theorem trivial_floor_collapse (G : Game.{u}) (B : Nat) (w : G.World) :
    (EGame (trivialCost G B)).floor (w, 0) ↔ G.floor w := by
  refine (egame_floor (trivialCost G B) w 0).trans ?_
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, Nat.zero_le B⟩

/-- **Degeneracy, both directions**: the controllable-predecessor of a base-floor-shaped region on the
`g = 0` slice of the zero-cost energy game is exactly the base game's `CPre` of that region. The grade
adds nothing when cost is `0` — energy safety degenerates to Boolean safety. -/
theorem trivial_CPre_collapse (G : Game.{u}) (B : Nat) (X : G.World → Prop) (w : G.World) :
    CPre (EGame (trivialCost G B)) (fun (p : EWorld (trivialCost G B)) => X p.1 ∧ p.2 = 0) (w, 0)
      ↔ CPre G X w := by
  unfold CPre
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, fun r hr => ?_⟩
    have hleg : (EGame (trivialCost G B)).legal (w, 0) m r := hr
    exact (hm r hleg).1
  · rintro ⟨m, hm⟩
    refine ⟨m, fun r hr => ?_⟩
    have hleg : G.legal w m r := hr
    refine ⟨?_, ?_⟩
    · exact hm r hleg
    · exact trivial_grade_stays G B w m r

/-! ## §6. The composed catch — ONE energy game refuses BOTH failure modes.

The Boolean `combineFloor` had to catch two *different* abuses on two axes. The energy floor catches
both with ONE accumulator:
  * **death-by-a-thousand-cuts** — many small costs that individually pass but SUM past the budget;
  * **a single big jump** — one cost already over the budget.
We exhibit a concrete tiny model and show, by `decide`, that the energy floor refuses both, while each
*individual* small cut is in budget (so the catch is genuinely cumulative, not a per-step bound). -/

section Demo

/-- A trivial one-state base game: the world is `Unit`, one move/resp, floor always holds. The energy
content lives entirely in the grade. -/
def unitBase : Game where
  World := Unit
  Move := Unit
  Resp := Unit
  step := fun _ _ _ => ()
  legal := fun _ _ _ => True
  floor := fun _ => True

/-- A cost game on `unitBase`: every transition costs `2`, budget `5`. Three cuts (`2+2+2 = 6 > 5`)
overrun; one cut (`2 ≤ 5`) does not — the death-by-a-thousand-cuts shape. -/
def cutsGame : CostGame where
  base := unitBase
  cost := fun _ _ _ => 2
  budget := 5

/-- The energy floor of `cutsGame`, as a DECIDABLE predicate on the grade (the base floor is `True`,
so the energy floor is exactly `g ≤ 5`). This is `(EGame cutsGame).floor ((), g)` reduced — the two
agree definitionally (`cutsFloor_eq`), and being a plain `g ≤ 5` it is decidable for the demos. -/
def cutsFloor (g : Nat) : Prop := g ≤ cutsGame.budget

instance : DecidablePred cutsFloor := fun g => inferInstanceAs (Decidable (g ≤ 5))

/-- `cutsFloor` IS the energy floor on the `Unit` slice (base floor `True` drops out). -/
theorem cutsFloor_eq (g : Nat) : (EGame cutsGame).floor ((), g) ↔ cutsFloor g := by
  refine (egame_floor cutsGame () g).trans ?_; exact ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩

/-- Accumulate `n` cuts from grade `0` via the energy step's `bump`. -/
def cutGrade : Nat → Nat
  | 0 => 0
  | n + 1 => bump cutsGame (cutGrade n) (2)

-- ONE cut is in budget (grade 2 ≤ 5): the energy floor admits it.
#guard decide (cutsFloor (cutGrade 1))
-- TWO cuts still in budget (grade 4 ≤ 5).
#guard decide (cutsFloor (cutGrade 2))
-- THREE cuts OVERRUN (grade 6 > 5): death-by-a-thousand-cuts is REFUSED by the energy floor.
#guard decide (¬ cutsFloor (cutGrade 3))

/-- **Death-by-a-thousand-cuts, refused — both polarities.** Each single cut is in budget (the floor
holds at one and two cuts) but the cumulative third cut overruns (the floor fails) — the energy floor
catches the *sum*, not any individual step. Stated on the energy floor itself via `cutsFloor_eq`. -/
theorem cuts_cumulative_refused :
    (EGame cutsGame).floor ((), cutGrade 1)
      ∧ (EGame cutsGame).floor ((), cutGrade 2)
      ∧ ¬ (EGame cutsGame).floor ((), cutGrade 3) := by
  refine ⟨(cutsFloor_eq _).2 ?_, (cutsFloor_eq _).2 ?_, fun h => ?_⟩
  · decide
  · decide
  · exact (by decide : ¬ cutsFloor (cutGrade 3)) ((cutsFloor_eq _).1 h)

/-- A cost game on `unitBase` with one BIG jump: a single transition costs `9 > 5 =` budget. -/
def jumpGame : CostGame where
  base := unitBase
  cost := fun _ _ _ => 9
  budget := 5

/-- The grade after a single jump step from `((), 0)`: `min (0 + 9) 6 = 6`. -/
theorem jump_grade : ((EGame jumpGame).step ((), 0) () ()).2 = 6 := by
  show bump jumpGame 0 9 = 6
  unfold bump GradeAlgebra.comp; decide

-- A single big jump OVERRUNS in one step (grade 6 > 5): REFUSED.
#guard decide (¬ ((((EGame jumpGame).step ((), 0) () ()).2) ≤ jumpGame.budget))

/-- **A single big jump, refused.** One transition whose cost exceeds the budget lands out of the
energy floor immediately. The SAME floor that catches the cumulative cuts catches the single jump. -/
theorem jump_refused :
    ¬ (EGame jumpGame).floor ((EGame jumpGame).step ((), 0) () ()) := by
  intro hfloor
  -- The energy floor demands `grade ≤ budget`; but the post-jump grade is `6 > 5`.
  have hg : ((EGame jumpGame).step ((), 0) () ()).2 ≤ jumpGame.budget :=
    ((egame_floor jumpGame _ _).1 hfloor).2
  rw [jump_grade] at hg
  exact absurd hg (by decide)

/-- **The composed catch as ONE game.** A start `((), 0)` is in budget; the cumulative third cut AND a
single big jump are BOTH out of the energy floor. One accumulator, both failure modes — the two-axis
`combineFloor` catch unified into a single energy game. -/
theorem composed_catch_one_game :
    (EGame cutsGame).floor ((), 0)
    ∧ ¬ (EGame cutsGame).floor ((), cutGrade 3)
    ∧ ¬ (EGame jumpGame).floor ((EGame jumpGame).step ((), 0) () ()) :=
  ⟨(cutsFloor_eq 0).2 (by decide),
   cuts_cumulative_refused.2.2,
   jump_refused⟩

-- Saturation works as intended: even far past the budget, the grade caps at `budget + 1` (here `6`),
-- so the energy world stays bounded — `bump` of an already-over grade does not run away.
#guard decide (bump cutsGame 100 2 = 6)
#guard decide (cutGrade 10 = 6)   -- ten cuts saturate at the sentinel, not 20

end Demo

/-! ## §7. Boolean degeneracy, concretely — the trivial energy game is the base game.

A zero-cost lift of `unitBase`: the floor is always met (base floor `True`, grade `0 ≤ B`), matching
the Boolean game with no energy content. -/

section TrivialDemo

/-- Zero-cost lift of `unitBase` at budget `3`. -/
def boolGame : CostGame := trivialCost unitBase 3

-- The grade never moves off `0` (cost ≡ 0); the floor is then the base floor `True` forever.
#guard decide ((boolGame.cost () () ()) = 0)
#guard decide (((EGame boolGame).step ((), 0) () ()).2 = 0)

/-- **Boolean degeneracy, concretely.** In the zero-cost lift, the energy floor on the `g = 0` slice is
exactly the base floor (`True` here), and the grade stays `0`: the energy game IS the Boolean game.
The floor half is `trivial_floor_collapse`; the grade half is `trivial_grade_stays`. -/
theorem bool_degenerate :
    (EGame boolGame).floor ((), 0)
      ∧ ((EGame boolGame).step ((), 0) () ()).2 = 0 :=
  ⟨(trivial_floor_collapse unitBase 3 ()).2 trivial,
   trivial_grade_stays unitBase 3 () () ()⟩

end TrivialDemo

/-! ## Axiom hygiene — the energy game's load-bearing facts. -/

#print axioms energy_safe
#print axioms winning_in_budget
#print axioms winning_invariant
#print axioms winning_maximal
#print axioms trivial_floor_collapse
#print axioms trivial_CPre_collapse
#print axioms cuts_cumulative_refused
#print axioms jump_refused
#print axioms composed_catch_one_game

/-!
The energy game, in one breath:

  1. EXPAND the world (`EWorld := World × Grade`); accumulate cost with the max-plus quantale `⊗ = +`,
     capped at `budget + 1` (`bump`). The energy floor is `base.floor ∧ grade ≤ budget`.
  2. The lift `EGame` is an ORDINARY `SafetyGame.Game` — so `ViabilityKernel`, `kernel_invariant`,
     `kernel_maximal`, `kernelShield`, `kernelShield_preserves` apply UNCHANGED. No new fixpoints.
  3. `GradedWinning := ViabilityKernel (EGame …)` IS the graded winning region (in-budget-forever);
     `energy_safe` shields it — the budget is never overrun, ∀ controller, ∀ tick.
  4. Boolean safety is the cost-≡-0 degenerate case (`trivial_floor_collapse`, `trivial_CPre_collapse`).
  5. ONE energy game refuses BOTH death-by-a-thousand-cuts AND a single big jump — the two-axis
     `combineFloor` catch unified into a single accumulator.
-/

end Metatheory.EnergyGame

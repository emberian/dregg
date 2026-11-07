/-
# `Dregg2.Crypto.RomQueryDial` — the query budget is LOAD-BEARING, because dialling it up FLIPS the
verdict at the same game.

`RomQueryFloor.romCollision_hard` proves the random-oracle collision floor against `RomEff F Q` at a
polynomially bounded `Q`. A floor with a hypothesis raises the question its own statement cannot
answer: is `hQ : PolyBounded ..` doing work, or is `Hard (romCollisionGame F) (RomEff F Q)` true for
every `Q`? In the second case `RomEff` would be a smallness condition that the budget merely
decorates, and `RomQueryFloor`'s escape from `FloorGames.hard_top_iff_solvableFrac_negl` would rest
on the tree shape alone.

## What this file settles

`romCollision_exhaustive_budget_false`: at `Q l = |D l|` — enough calls to read the oracle's whole
truth table — the floor is FALSE. The class `RomEff F Q` then contains `bruteComp`, which queries
every domain point, reconstructs `H` from the answers, and returns a collision. It wins on EVERY
oracle (pigeonhole, `RomQueryFloor.romCollision_always_solvable`), so its advantage is the constant
`1`, refuted by `ConcreteSecurity.not_negl_one`.

`binaryRom_budget_separates` states the consequence at the deployed family: at `Q l = l` the floor
holds (`RomQueryFloor.binaryRom_hard_linear_budget`), at `Q l = 2·2^l` it does not. Same game, same
win relation, same class SHAPE — only the budget differs, and the verdict flips. `Q` is a dial
between the two horns.

## ⚑ What the budget bounds is CALLS, not thought

`bruteComp` is `noncomputable` and uses `Classical.choice` twice over: `reconstruct` rebuilds the
oracle from the answer list, and `pickColl` selects a collision out of the reconstructed function by
`Exists.choose`. That is not a defect of the construction — it is the model's content. `RomOracle.
QueryBounded` bounds the number of oracle calls along a path and says nothing whatever about the
continuations `k : R → OracleComp ..`, which are arbitrary Lean functions. `bruteComp` is
`FloorGames.choiceAdv` in every respect except one: it PAYS for its knowledge of `H`, one query per
domain point. `RomQueryFloor.choiceAdv_not_romEff` excludes `choiceAdv` from the class at a
polynomial budget because it knows without asking; `bruteComp` asks, and at an exhaustive budget it
is admitted, and the floor falls. The exclusion is about queries and nothing else.

This is the residual `RomQueryFloor` names, seen from the other side: the budget is a query count,
not a running time, and `bruteComp` shows exactly how much an unbounded-thought adversary can buy
with `|D l|` calls — everything.

## Axiom hygiene

`#assert_all_clean` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`, no fresh `axiom`, no
`native_decide`.
-/
import Dregg2.Crypto.RomQueryFloor
import Dregg2.Tactics
import Mathlib.Tactic

namespace Dregg2.Crypto.RomQueryDial

open Dregg2.Crypto.ConcreteSecurity (not_negl_one)
open Dregg2.Crypto.FloorGames (Adversary Hard gameAdv)
open Dregg2.Crypto.RomOracle (OracleComp QueryBounded)
open Dregg2.Crypto.RomQueryFloor
  (RomFamily RomComp RomEff romAdv romCollisionGame romCollision_always_solvable binaryRomFamily
   binaryRom_compressing binaryRom_hard_linear_budget)

set_option autoImplicit false

/-! ## §1 — RECONSTRUCTION: the answers to every domain point ARE the oracle. -/

/-- **THE ORACLE, REBUILT FROM AN ANSWER LIST.** `reconstruct ds rs d0` reads `x`'s answer off `rs`
at `x`'s position in `ds`, falling back to `d0` when `x` does not occur. It is the only thing a
query tree ever has: a list of points it asked about and a list of what came back. -/
def reconstruct {D R : Type} [DecidableEq D] (ds : List D) (rs : List R) (d0 : R) : D → R :=
  fun x => rs.getD (ds.idxOf x) d0

/-- **READING EVERY POINT RECOVERS THE ORACLE.** When `ds` meets the whole domain, the answers to
`ds` determine `H` exactly. `List.idxOf` returns the FIRST occurrence and `ds[ds.idxOf x] = x` holds
for every `x ∈ ds`, so duplicates in `ds` do no harm and `ds.Nodup` is not needed. -/
theorem reconstruct_map {D R : Type} [DecidableEq D] (ds : List D) (hall : ∀ x : D, x ∈ ds)
    (H : D → R) (d0 : R) : reconstruct ds (ds.map H) d0 = H := by
  funext x
  show (ds.map H).getD (ds.idxOf x) d0 = H x
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_idxOf (hall x)]
  rfl

/-! ## §2 — the brute-force attack: read the whole oracle, then choose a collision. -/

/-- **THE COLLISION, CHOSEN.** Given the oracle in hand, pick a collision of it wherever one exists.
`Exists.choose` — the same non-constructive selection `FloorGames.choiceAdv` performs. What §3 does
differently is PAY for the oracle: `pickColl` is applied only to a function reconstructed from
`|D l|` answers that were actually asked for. -/
noncomputable def pickColl (F : RomFamily) (l : ℕ) (H : F.D l → F.R l) : F.D l × F.D l :=
  letI := Classical.propDecidable (∃ p : F.D l × F.D l, p.1 ≠ p.2 ∧ H p.1 = H p.2)
  if h : ∃ p : F.D l × F.D l, p.1 ≠ p.2 ∧ H p.1 = H p.2 then h.choose
  else ((F.dNe l).some, (F.dNe l).some)

/-- **THE CHOSEN PAIR IS A COLLISION, AT EVERY ORACLE OF A COMPRESSING FAMILY.** Pigeonhole supplies
the existence (`RomQueryFloor.romCollision_always_solvable`), so the `dif` takes its positive branch
and `Exists.choose_spec` is the win. -/
theorem pickColl_wins (F : RomFamily)
    (hc : ∀ l, letI := F.dFin l; letI := F.rFin l;
      Fintype.card (F.R l) < Fintype.card (F.D l))
    (l : ℕ) (H : (romCollisionGame F).Inst l) :
    (romCollisionGame F).wins l H (pickColl F l H) := by
  have hex : ∃ p : F.D l × F.D l, p.1 ≠ p.2 ∧ H p.1 = H p.2 :=
    romCollision_always_solvable F hc l H
  simp only [pickColl, dif_pos hex]
  exact hex.choose_spec

/-- **⚑ THE BRUTE-FORCE QUERY TREE.** It queries EVERY point of the domain in turn, rebuilds `H`
from the answers, and returns a collision of it.

⚑ It is `noncomputable`, and its continuation is `Classical.choice` — deliberately. `RomOracle.
QueryBounded` bounds oracle CALLS along a path; the continuations are arbitrary Lean functions and
this file's point is that they may be as non-constructive as they like. A query-bounded adversary is
restricted in what it ASKS, not in what it THINKS. This tree is `FloorGames.choiceAdv` in every
respect except that it pays for its knowledge of `H`, one query per domain point — and §4 shows the
price is affordable exactly when the budget reaches `|D l|`. -/
noncomputable def bruteComp (F : RomFamily) (l : ℕ) :
    OracleComp (F.D l) (F.R l) (F.D l × F.D l) :=
  letI := F.dFin l; letI := F.dDec l
  OracleComp.ofList Finset.univ.toList (fun rs =>
    pickColl F l (reconstruct Finset.univ.toList rs (F.rNe l).some))

/-- **THE BRUTE-FORCE TREE COSTS EXACTLY `|D l|` QUERIES.** `Finset.univ.toList` has length
`Fintype.card (F.D l)`, and `RomOracle.OracleComp.ofList_queryBounded` charges one query per entry.
-/
theorem bruteComp_bounded (F : RomFamily) (l : ℕ) :
    QueryBounded (letI := F.dFin l; Fintype.card (F.D l)) (bruteComp F l) := by
  letI := F.dFin l; letI := F.dDec l
  have h := OracleComp.ofList_queryBounded (D := F.D l) (R := F.R l)
    (Finset.univ.toList) (fun rs =>
      pickColl F l (reconstruct Finset.univ.toList rs (F.rNe l).some))
  rw [Finset.length_toList, Finset.card_univ] at h
  exact h

/-- **RUN AGAINST `H`, THE BRUTE-FORCE TREE HOLDS `H` ITSELF.** `ofList_eval` says the continuation
receives `Finset.univ.toList.map H`, and `reconstruct_map` says that answer list rebuilds `H`
exactly. The tree never reads the oracle; it buys it. -/
theorem bruteComp_eval (F : RomFamily) (l : ℕ) (H : F.D l → F.R l) :
    (bruteComp F l).eval H = pickColl F l H := by
  letI := F.dFin l; letI := F.dDec l
  show (OracleComp.ofList Finset.univ.toList (fun rs =>
      pickColl F l (reconstruct Finset.univ.toList rs (F.rNe l).some))).eval H = _
  rw [OracleComp.ofList_eval,
    reconstruct_map Finset.univ.toList (fun x => Finset.mem_toList.2 (Finset.mem_univ x)) H]

/-! ## §3 — the brute-force adversary wins on EVERY instance. -/

/-- **IT WINS EVERYWHERE.** At every oracle of a compressing family the brute-force adversary's
answer is a genuine collision: it has `H` in hand, and a collision exists. -/
theorem bruteAdv_hit (F : RomFamily)
    (hc : ∀ l, letI := F.dFin l; letI := F.rFin l;
      Fintype.card (F.R l) < Fintype.card (F.D l))
    (l : ℕ) (H : (romCollisionGame F).Inst l) :
    (romAdv F (bruteComp F)).hit l H = true := by
  refine (Adversary.hit_eq_true _ _ _).mpr ?_
  show (romCollisionGame F).wins l H ((bruteComp F l).eval H)
  erw [bruteComp_eval]
  exact pickColl_wins F hc l H

/-- **ITS ADVANTAGE IS THE CONSTANT `1`.** Winning on every instance makes the win fraction `1`
(`ProbCrypto.winProb_top`) — the same value `FloorGames.solvableFrac` takes at this family, reached
here by an adversary that is in `RomEff F (fun l => |D l|)`. -/
theorem bruteAdv_gameAdv (F : RomFamily)
    (hc : ∀ l, letI := F.dFin l; letI := F.rFin l;
      Fintype.card (F.R l) < Fintype.card (F.D l)) :
    gameAdv (romCollisionGame F) (romAdv F (bruteComp F)) = fun _ => (1 : ℝ) := by
  funext l
  unfold gameAdv
  rw [show ((romAdv F (bruteComp F)).hit l) = (fun _ => true) from
    funext (fun H => bruteAdv_hit F hc l H)]
  exact @Dregg2.Crypto.ProbCrypto.winProb_top _ ((romCollisionGame F).instFin l)
    ((romCollisionGame F).instNe l)

/-- **THE BRUTE-FORCE ADVERSARY IS IN THE CLASS AT AN EXHAUSTIVE BUDGET.** It factors through
`bruteComp`, by definition, and `bruteComp` fits the budget `|D l|`. -/
theorem bruteAdv_in_romEff (F : RomFamily) :
    RomEff F (fun l => letI := F.dFin l; Fintype.card (F.D l)) (romAdv F (bruteComp F)) :=
  ⟨bruteComp F, fun l => bruteComp_bounded F l, fun _ _ => rfl⟩

/-! ## §4 — ⚑ THE BUDGET IS LOAD-BEARING. -/

/-- **⚑ THE BUDGET IS LOAD-BEARING — at a budget large enough to read the whole oracle, the floor is
FALSE.**

`RomQueryFloor.romCollision_hard` carries `hQ : PolyBounded ..`, and this theorem is what makes that
hypothesis content rather than decoration: at `Q l = |D l|` the SAME floor at the SAME game is
refuted. `RomEff F Q` is therefore not a smallness condition that holds for every budget, and
`RomQueryFloor`'s escape from `FloorGames.hard_top_iff_solvableFrac_negl` is not a property of the
`OracleComp` shape alone. The witness is `bruteComp`: it makes `|D l|` calls, learns `H`, and wins
with probability `1`. -/
theorem romCollision_exhaustive_budget_false (F : RomFamily)
    (hc : ∀ l, letI := F.dFin l; letI := F.rFin l;
      Fintype.card (F.R l) < Fintype.card (F.D l)) :
    ¬ Hard (romCollisionGame F) (RomEff F (fun l => letI := F.dFin l; Fintype.card (F.D l))) := by
  intro hhard
  have hnegl := hhard _ (bruteAdv_in_romEff F)
  rw [bruteAdv_gameAdv F hc] at hnegl
  exact not_negl_one hnegl

/-! ## §5 — the dial, at the deployed family. -/

/-- The deployed family's domain has `2·2^λ` points. -/
theorem binaryRom_card_D (l : ℕ) :
    letI := binaryRomFamily.dFin l
    Fintype.card (binaryRomFamily.D l) = 2 * 2 ^ l := by
  show Fintype.card (Fin (2 * 2 ^ l)) = 2 * 2 ^ l
  simp only [Fintype.card_fin]

/-- **THE FLOOR IS FALSE AT THE DEPLOYED FAMILY, AT AN EXHAUSTIVE BUDGET.** `2·2^λ` queries read the
whole `λ`-bit-digest oracle, and the brute-force adversary in that class wins always. -/
theorem binaryRom_exhaustive_budget_false :
    ¬ Hard (romCollisionGame binaryRomFamily)
        (RomEff binaryRomFamily (fun l => 2 * 2 ^ l)) := by
  have h := romCollision_exhaustive_budget_false binaryRomFamily binaryRom_compressing
  rwa [show (fun l => letI := binaryRomFamily.dFin l; Fintype.card (binaryRomFamily.D l))
      = (fun l => 2 * 2 ^ l) from funext binaryRom_card_D] at h

/-- **⚑⚑ THE DIAL IS REAL.** At the SAME game: a linear budget gives a TRUE floor
(`RomQueryFloor.binaryRom_hard_linear_budget`), an exhaustive budget gives a FALSE one. `Q` is not
decoration. -/
theorem binaryRom_budget_separates :
    Hard (romCollisionGame binaryRomFamily) (RomEff binaryRomFamily (fun l => l))
      ∧ ¬ Hard (romCollisionGame binaryRomFamily) (RomEff binaryRomFamily (fun l => 2 * 2 ^ l)) :=
  ⟨binaryRom_hard_linear_budget, binaryRom_exhaustive_budget_false⟩

/-- **(TOOTH — the two budgets are not the same class.)** `RomEff binaryRomFamily (fun l => l)` and
`RomEff binaryRomFamily (fun l => 2·2^l)` are distinct predicates on the same `Adversary` type: one
satisfies the floor, the other does not. The budget parameter separates classes, so `RomEff` is a
family and not a constant. -/
theorem binaryRom_romEff_budget_ne :
    RomEff binaryRomFamily (fun l => l) ≠ RomEff binaryRomFamily (fun l => 2 * 2 ^ l) := by
  intro h
  refine binaryRom_exhaustive_budget_false ?_
  rw [← h]
  exact binaryRom_hard_linear_budget

/-- **(TOOTH — the brute-force adversary is EXCLUDED at the linear budget.)** The dial's other end,
stated about the witness itself: `bruteComp`'s adversary is in `RomEff binaryRomFamily (fun l => 2·
2^l)` (`bruteAdv_in_romEff`) but not in `RomEff binaryRomFamily (fun l => l)` — if it were, the
linear-budget floor would make its advantage, the constant `1`, negligible. So the budget does not
merely change which `Prop` is provable; it changes membership. -/
theorem bruteAdv_not_romEff_linear :
    ¬ RomEff binaryRomFamily (fun l => l) (romAdv binaryRomFamily (bruteComp binaryRomFamily)) := by
  intro hmem
  have hnegl := binaryRom_hard_linear_budget _ hmem
  rw [bruteAdv_gameAdv binaryRomFamily binaryRom_compressing] at hnegl
  exact not_negl_one hnegl

/-! ## Kernel-clean keystones. -/

#assert_all_clean [
  reconstruct_map,
  pickColl_wins,
  bruteComp_bounded,
  bruteComp_eval,
  bruteAdv_hit,
  bruteAdv_gameAdv,
  bruteAdv_in_romEff,
  romCollision_exhaustive_budget_false,
  binaryRom_card_D,
  binaryRom_exhaustive_budget_false,
  binaryRom_budget_separates,
  binaryRom_romEff_budget_ne,
  bruteAdv_not_romEff_linear
]

end Dregg2.Crypto.RomQueryDial

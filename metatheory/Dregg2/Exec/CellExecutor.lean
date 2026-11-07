/-
# Dregg2.Exec.CellExecutor — living-cell executor bundle.

**Production** = `CellExecutor.production` (`execForestG`, credential+caveat+revocation gate).

`CellExecutor.kernelForest` is NOT a second product entry — it is the forest kernel body inside
`execFullAGated` (`if gateOK then execFullA else none`). It exists only so erasure lemmas can reuse
kernel conservation/grow proofs; nothing user-facing should treat it as runnable semantics.
-/
import Dregg2.Exec.CellCarry
import Dregg2.Exec.GatedForestCfg

namespace Dregg2.Exec

open Dregg2.Authority (Label)
open Dregg2.Exec.TurnExecutorFull
open FullForest
open FullForestAuth (lowerForestG_actions_eq_eraseG lowerForestG)
open StarbridgeGated (Dg Pf Rq St Wt Cx Gw Bt Tg DForest DChild execForestG execForestG_erases eraseForestG)

/-- **Living-cell executor bundle.** -/
structure CellExecutor where
  Forest : Type
  Conserving : Type
  toForest : Conserving → Forest
  exec : RecChainedState → Forest → Option RecChainedState
  next (s : RecChainedState) (c : Conserving) : RecChainedState :=
    (exec s (toForest c)).getD s
  TurnSched : Type
  traj : RecChainedState → TurnSched → Nat → RecChainedState

/-- Forever-carry capability for a living-cell executor. -/
class CellCarries (E : CellExecutor) where
  carries : ∀ (Good : RecChainedState → Prop)
    (hpres : ∀ s c, Good s → Good (E.next s c))
    (s : RecChainedState) (hinit : Good s) (sched : E.TurnSched),
    ∀ n, Good (E.traj s sched n)

/-! ## Kernel forest (internal — auth-stripped body for erasure reuse only). -/

namespace CellExecutor

noncomputable def kernelForest : CellExecutor where
  Forest := FullForestA
  Conserving := ConservingForest
  toForest cf := cf.1
  exec := execFullForestA
  TurnSched := SchedA
  traj := trajA

theorem kernelForest_next_eq (s : RecChainedState) (cf : ConservingForest) :
    kernelForest.next s cf = cellNextA s cf := rfl

theorem kernelForest_forever (Good : RecChainedState → Prop)
    (hpres : ∀ s cf, Good s → Good (kernelForest.next s cf))
    (s : RecChainedState) (hinit : Good s) (sched : SchedA) :
    ∀ n, Good (kernelForest.traj s sched n) :=
  livingCellA_carries Good (fun s cf h => by simpa [kernelForest_next_eq] using hpres s cf h) s hinit sched

instance kernelForestCarries : CellCarries kernelForest where
  carries := kernelForest_forever

end CellExecutor

/-! ## Production executor (starbridge carriers + gated forest). -/

def ConservingGatedForest : Type :=
  { f : DForest // ∀ b, turnLedgerDeltaAsset ((lowerForestG f).map Prod.snd) b = 0 }

noncomputable def cellNextG (s : RecChainedState) (cg : ConservingGatedForest) : RecChainedState :=
  (execForestG s cg.val).getD s

noncomputable def conservingGated_erase (cg : ConservingGatedForest) : ConservingForest :=
  ⟨eraseForestG cg.val, by
    intro b
    dsimp [eraseForestG]
    rw [← lowerForestG_actions_eq_eraseG cg.val]
    exact cg.property b⟩

theorem cellNextG_eq_cellNextA_on_commit (s s' : RecChainedState) (cg : ConservingGatedForest)
    (h : execForestG s cg.val = some s') :
    cellNextG s cg = cellNextA s (conservingGated_erase cg) := by
  dsimp [cellNextG, cellNextA, conservingGated_erase]
  rw [h, Option.getD_some]
  have er := execForestG_erases s s' cg.val h
  rw [← er.symm, Option.getD_some]

theorem cellNextG_preserves_kernelForest (Good : RecChainedState → Prop)
    (hpres : ∀ s cf, Good s → Good (cellNextA s cf))
    (s : RecChainedState) (cg : ConservingGatedForest) (h : Good s) :
    Good (cellNextG s cg) := by
  unfold cellNextG
  cases hc : execForestG s cg.val with
  | none    => simp only [Option.getD_none]; exact h
  | some s' =>
      simp only [Option.getD_some]
      have er := execForestG_erases s s' cg.val hc
      have hnext : cellNextA s (conservingGated_erase cg) = s' := by
        dsimp [cellNextA, conservingGated_erase]
        rw [er, Option.getD_some]
      rw [← hnext]
      exact hpres s (conservingGated_erase cg) h

abbrev SchedG : Type := Nat → ConservingGatedForest

noncomputable def trajG (s : RecChainedState) (sched : SchedG) : Nat → RecChainedState
  | 0     => s
  | n + 1 => cellNextG (trajG s sched n) (sched n)

theorem livingCellG_carries (Good : RecChainedState → Prop)
    (hpres : ∀ s cg, Good s → Good (cellNextG s cg))
    (s : RecChainedState) (hinit : Good s) (sched : SchedG) :
    ∀ n, Good (trajG s sched n) := by
  intro n
  induction n with
  | zero => exact hinit
  | succ k ih =>
      show Good (cellNextG (trajG s sched k) (sched k))
      exact hpres _ _ ih

theorem hpresG_of_kernelForest (Good : RecChainedState → Prop)
    (hpresA : ∀ s cf, Good s → Good (cellNextA s cf)) :
    ∀ s cg, Good s → Good (cellNextG s cg) :=
  fun s cg h => cellNextG_preserves_kernelForest Good hpresA s cg h

namespace CellExecutor

/-- **The production living-cell executor** — gated starbridge forest turns. -/
noncomputable def production : CellExecutor where
  Forest := DForest
  Conserving := ConservingGatedForest
  toForest cg := cg.val
  exec s f := execForestG s f
  TurnSched := SchedG
  traj := trajG

theorem production_next_eq (s : RecChainedState) (cg : ConservingGatedForest) :
    production.next s cg = cellNextG s cg := by
  dsimp [CellExecutor.next, cellNextG, production]

theorem production_erases_kernelForest (Good : RecChainedState → Prop)
    (hpresA : ∀ s cf, Good s → Good (cellNextA s cf)) :
    ∀ s cg, Good s → Good (production.next s cg) := by
  intro s cg h
  rw [production_next_eq s cg]
  exact hpresG_of_kernelForest Good hpresA s cg h

theorem production_forever (Good : RecChainedState → Prop)
    (hpres : ∀ s cg, Good s → Good (production.next s cg))
    (s : RecChainedState) (hinit : Good s) (sched : SchedG) :
    ∀ n, Good (production.traj s sched n) :=
  livingCellG_carries Good (fun s cg h => by simpa [production_next_eq] using hpres s cg h) s hinit sched

instance productionCarries : CellCarries production where
  carries := production_forever

/-- Back-compat alias — prefer `production`. -/
noncomputable abbrev gated := production

end CellExecutor

theorem cellObsG_next (s : RecChainedState) (cg : ConservingGatedForest) :
    cellObsA (cellNextG s cg) = cellObsA s :=
  cellNextG_preserves_kernelForest (fun s' => cellObsA s' = cellObsA s)
    (fun a cf h => by show cellObsA (cellNextA a cf) = cellObsA s; rw [cellObsA_next]; exact h)
    s cg rfl

def AlwaysG (P : RecChainedState → Prop) (s : RecChainedState) (sched : SchedG) : Prop :=
  ∀ n, P (trajG s sched n)

theorem alwaysG_of_step_invariant (P : RecChainedState → Prop)
    (hpres : ∀ s cf, P s → P (cellNextG s cf))
    (s : RecChainedState) (hinit : P s) (sched : SchedG) :
    AlwaysG P s sched :=
  livingCellG_carries P hpres s hinit sched

theorem alwaysG_of_kernelForest_step (P : RecChainedState → Prop)
    (hpresA : ∀ s cf, P s → P (cellNextA s cf))
    (s : RecChainedState) (hinit : P s) (sched : SchedG) :
    AlwaysG P s sched :=
  alwaysG_of_step_invariant P (hpresG_of_kernelForest P hpresA) s hinit sched

#assert_axioms cellNextG_eq_cellNextA_on_commit
#assert_axioms cellNextG_preserves_kernelForest
#assert_axioms cellObsG_next
#assert_axioms livingCellG_carries
#assert_axioms hpresG_of_kernelForest

end Dregg2.Exec
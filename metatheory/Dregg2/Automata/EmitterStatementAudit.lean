/- Source-bound statement evidence for shared generated arithmetic AIR.
These checks exercise emitted expressions, not a second implementation.
Full descriptor/lookup witnesses remain in their owning modules. -/
import Dregg2.Circuit.Emit.SolvencyLeafEmit
import Dregg2.Circuit.Emit.TupleBindingEmit
import Dregg2.Circuit.Emit.BorrowChainEmit
import Dregg2.Circuit.Emit.CaveatAdmissionEmit
import Dregg2.Circuit.Emit.DecoLeafEmit
namespace Dregg2.Automata.EmitterStatementAudit
open Dregg2.Circuit.Emit
open Dregg2.Exec.CircuitEmit
set_option autoImplicit false

/-- Dropping reconstruction accepts canonical value 2 with zero Boolean bits;
the actual one-bit range generator refuses the same assignment. -/
theorem range_reconstruction_separation :
    let a : Nat → Int := fun c => if c = 0 then 2 else 0
    ([BoundedFactEmit.boolean 1].all (fun e => decide (e.eval a ≡ 0 [ZMOD 2013265921]))) = true ∧
    ((BoundedFactEmit.rangeBodies 1 0 1).all
      (fun e => decide (e.eval a ≡ 0 [ZMOD 2013265921]))) = false := by decide

/-- The actual soundness theorem fires on an inhabited canonical assignment. -/
theorem range_sound_inhabited : (0 : Int) ≤ 0 ∧ (0 : Int) < 2^1 := by
  exact BoundedFactEmit.rangeBodies_sound (fun _ => 0) 1 0 1 (by decide)
    (fun _ => by constructor <;> norm_num) (by
      intro e he
      simp [BoundedFactEmit.rangeBodies] at he
      rcases he with rfl | rfl <;>
        simp [BoundedFactEmit.boolean, BoundedFactEmit.sub,
          BoundedFactEmit.recompose, EmittedExpr.eval])

def underflowRow (c : Nat) : Int := if c = 0 then 1 else if c = 2 then 9 else 0
def underflowBorrow (j : Nat) : EmittedExpr := .const (if j = 0 then 0 else 1)

/-- Same emitted limb equations and ranged Boolean operands: dropping the final
borrow accepts 1≤0; the final-zero envelope refuses it. -/
theorem borrow_underflow_separation :
    let checks := (BorrowChainEmit.bodies 10 1 (fun _ => 0) (fun _ => 1)
      (fun _ => 2) underflowBorrow).all
        (fun e => decide (e.eval underflowRow ≡ 0 [ZMOD 2013265921]))
    checks = true ∧
    (checks && decide ((underflowBorrow 1).eval underflowRow = 0)) = false ∧
    underflowRow 0 > underflowRow 1 ∧
    (0 ≤ underflowRow 0 ∧ underflowRow 0 < 10) ∧
    (0 ≤ underflowRow 1 ∧ underflowRow 1 < 10) ∧
    (0 ≤ underflowRow 2 ∧ underflowRow 2 < 10) ∧
    (underflowBorrow 0).eval underflowRow = 0 ∧
    (underflowBorrow 1).eval underflowRow = 1 := by decide

/-- The arbitrary-width theorem is inhabited, including its final-zero premise. -/
theorem borrow_sound_inhabited : (0 : Int) ≤ 0 := by
  exact BorrowChainEmit.bodies_sound 10 1 (fun _ => 0) (fun _ => 1)
    (fun _ => 2) (fun _ => .const 0) (fun _ => 0) (by decide) (by decide)
    (fun _ _ => by norm_num) (fun _ _ => Or.inl rfl) rfl
    (BorrowChainEmit.zero_chain_holds 10 1 _ _ _)

/-- All arithmetic, chip and canonical public premises hold simultaneously. -/
theorem solvency_main_fires :
    SolvencyLeafEmit.honestTrace.pub 0 = 0 ∧ SolvencyLeafEmit.honestTrace.pub 1 = 0 := by
  exact SolvencyLeafEmit.solvency_commitments_sound (fun _ => List.replicate 8 0)
    (by decide) SolvencyLeafEmit.honest_canonical
    (fun _ _ => by constructor <;> norm_num [SolvencyLeafEmit.honestTrace])
    SolvencyLeafEmit.honest_chip_sound SolvencyLeafEmit.honest_satisfies

/-- The public four-atom theorem fires with the faithful range table, at height one. -/
theorem caveat_main_fires :
    let p := CaveatAdmissionEmit.honestTrace.pub
    CaveatAdmissionEmit.amount p 0 ≤ CaveatAdmissionEmit.amount p 1 ∧
    CaveatAdmissionEmit.amount p 2 < CaveatAdmissionEmit.amount p 3 ∧
    CaveatAdmissionEmit.amount p 4 ≤ CaveatAdmissionEmit.amount p 5 ∧
    CaveatAdmissionEmit.amount p 6 = CaveatAdmissionEmit.amount p 7 := by
  exact CaveatAdmissionEmit.caveat_public_sound (by decide)
    (by simp only [CaveatAdmissionEmit.honestTrace, CaveatAdmissionEmit.honestTable, ↓reduceIte])
    CaveatAdmissionEmit.honest_canonical
    (fun k _ => CaveatAdmissionEmit.honest_canonical k)
    CaveatAdmissionEmit.honest_satisfies

/-- The emitted payment identity opens the same public tuple as its range proof. -/
theorem deco_main_fires :
    let p := DecoLeafEmit.honestTrace.pub
    p 4 = DecoLeafEmit.paymentIdentity (fun _ => List.replicate 8 0) (p 0) (p 1) (p 2) (p 3) := by
  exact DecoLeafEmit.payment_identity (fun _ => List.replicate 8 0) (by decide)
    DecoLeafEmit.honest_canonical (fun k _ => DecoLeafEmit.honest_canonical k)
    DecoLeafEmit.honest_chip_sound DecoLeafEmit.honest_satisfies

/-- info: 'Dregg2.Automata.EmitterStatementAudit.solvency_main_fires' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms solvency_main_fires
/-- info: 'Dregg2.Automata.EmitterStatementAudit.caveat_main_fires' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms caveat_main_fires
/-- info: 'Dregg2.Automata.EmitterStatementAudit.deco_main_fires' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms deco_main_fires

/-- info: 'Dregg2.Automata.EmitterStatementAudit.range_reconstruction_separation' depends on axioms: [propext] -/
#guard_msgs in
#print axioms range_reconstruction_separation
/-- info: 'Dregg2.Automata.EmitterStatementAudit.range_sound_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms range_sound_inhabited
/-- info: 'Dregg2.Automata.EmitterStatementAudit.borrow_underflow_separation' does not depend on any axioms -/
#guard_msgs in
#print axioms borrow_underflow_separation
/-- info: 'Dregg2.Automata.EmitterStatementAudit.borrow_sound_inhabited' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms borrow_sound_inhabited
/-- info: 'Dregg2.Circuit.Emit.SolvencyLeafEmit.old_modular_difference_accepts_30bit_insolvent' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SolvencyLeafEmit.old_modular_difference_accepts_30bit_insolvent
/-- info: 'Dregg2.Circuit.Emit.SolvencyLeafEmit.arithmetic_refuses_insolvent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SolvencyLeafEmit.arithmetic_refuses_insolvent
/-- info: 'Dregg2.Circuit.Emit.SolvencyLeafEmit.honest_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolvencyLeafEmit.honest_canonical
/-- info: 'Dregg2.Circuit.Emit.SolvencyLeafEmit.honest_chip_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SolvencyLeafEmit.honest_chip_sound
/-- info: 'Dregg2.Circuit.Emit.CaveatAdmissionEmit.strict_boundary_falsifier' does not depend on any axioms -/
#guard_msgs in
#print axioms CaveatAdmissionEmit.strict_boundary_falsifier
/-- info: 'Dregg2.Circuit.Emit.CaveatAdmissionEmit.honest_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CaveatAdmissionEmit.honest_canonical
end Dregg2.Automata.EmitterStatementAudit

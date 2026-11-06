/- Generic field-safe borrow chains. Gates are authored here; Rust only fills witnesses. -/
import Dregg2.Circuit.Emit.BoundedFactEmit
import Dregg2.Circuit.CaveatBignumCompare
namespace Dregg2.Circuit.Emit.BorrowChainEmit
open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.DescriptorIR2
set_option autoImplicit false

/-- Little-endian value of a fixed number of limbs; width is a generator parameter. -/
def value (B : Int) : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n+1, a => a 0 + B * value B n (fun j => a (j+1))

/-- The exact expression tree used by the existing caveat producer. -/
def limbBody (B : Int) (x y d : Nat) (incoming outgoing : EmittedExpr) : EmittedExpr :=
  .add (.add (.add (.add (.var d) (.mul (.const (-1)) (.var y))) (.var x)) incoming)
    (.mul (.const (-B)) outgoing)

def bodies (B : Int) (n : Nat) (x y d : Nat → Nat) (borrow : Nat → EmittedExpr) :
    List EmittedExpr :=
  (List.range n).map (fun j => limbBody B (x j) (y j) (d j) (borrow j) (borrow (j+1)))

/-- A modular limb equation has one integer interpretation when two radix limbs fit. -/
theorem modular_limb_sound (B x y d incoming outgoing : Int)
    (hB : 0 < B) (hfit : 2 * B < 2013265921)
    (hx : 0 ≤ x ∧ x < B) (hy : 0 ≤ y ∧ y < B) (hd : 0 ≤ d ∧ d < B)
    (hi : incoming = 0 ∨ incoming = 1) (ho : outgoing = 0 ∨ outgoing = 1)
    (he : d - y + x + incoming - B * outgoing ≡ 0 [ZMOD 2013265921]) :
    d = y - x - incoming + B * outgoing := by
  obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp he
  rcases hi with rfl | rfl <;> rcases ho with rfl | rfl <;> simp only [mul_zero, mul_one] at * <;>
    omega

/-- Telescoping the generated chain, with no final borrow, gives exact subtraction. -/
theorem chain_identity (B : Int) : ∀ (n : Nat) (x y d borrow : Nat → Int),
    (∀ j < n, d j = y j - x j - borrow j + B * borrow (j+1)) → borrow n = 0 →
    value B n d = value B n y - value B n x - borrow 0 := by
  intro n
  induction n with
  | zero => intro x y d borrow _ hb; simpa [value] using hb
  | succ n ih =>
    intro x y d borrow he hb
    have hh := ih (fun j => x (j+1)) (fun j => y (j+1))
      (fun j => d (j+1)) (fun j => borrow (j+1))
      (fun j hj => he (j+1) (by omega)) hb
    have h0 := he 0 (by omega)
    simp only [value]
    rw [hh, h0]
    ring

theorem value_nonneg (B : Int) (hB : 0 ≤ B) : ∀ (n : Nat) (a : Nat → Int),
    (∀ j < n, 0 ≤ a j) → 0 ≤ value B n a := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro a ha
    have h0 := ha 0 (by omega)
    have ht := ih (fun j => a (j+1)) (fun j hj => ha (j+1) (by omega))
    simp only [value]
    positivity

/-- Generic soundness for the actual emitted expression list at any limb width. -/
theorem bodies_sound (B : Int) (n : Nat) (x y d : Nat → Nat) (borrow : Nat → EmittedExpr)
    (a : Assignment) (hB : 0 < B) (hfit : 2 * B < 2013265921)
    (hr : ∀ j < n, (0 ≤ a (x j) ∧ a (x j) < B) ∧
      (0 ≤ a (y j) ∧ a (y j) < B) ∧ (0 ≤ a (d j) ∧ a (d j) < B))
    (hb : ∀ j ≤ n, (borrow j).eval a = 0 ∨ (borrow j).eval a = 1)
    (htop : (borrow n).eval a = 0)
    (he : ∀ e ∈ bodies B n x y d borrow, e.eval a ≡ 0 [ZMOD 2013265921]) :
    value B n (fun j => a (x j)) + (borrow 0).eval a ≤
      value B n (fun j => a (y j)) := by
  have eqn : ∀ j < n, a (d j) = a (y j) - a (x j) - (borrow j).eval a +
      B * (borrow (j+1)).eval a := by
    intro j hj
    apply modular_limb_sound B _ _ _ _ _ hB hfit (hr j hj).1 (hr j hj).2.1
      (hr j hj).2.2 (hb j (by omega)) (hb (j+1) (by omega))
    have hh := he _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
    simpa [limbBody, EmittedExpr.eval, sub_eq_add_neg, add_assoc, neg_mul] using hh
  have hi := chain_identity B n (fun j => a (x j)) (fun j => a (y j))
    (fun j => a (d j)) (fun j => (borrow j).eval a) eqn htop
  have hn := value_nonneg B (by omega) n (fun j => a (d j)) (fun j hj => (hr j hj).2.2.1)
  dsimp only at hi
  omega

/-- Removing the top-borrow condition would admit an underflow (base10, one limb). -/
theorem top_borrow_falsifier : (0 : Int) < 1 ∧ (9 : Int) = 0 - 1 - 0 + 10 * 1 := by decide

/-- Every width has an inhabitant: all-zero limbs and zero incoming/final borrows. -/
theorem zero_chain_holds (B : Int) (n : Nat) (x y d : Nat → Nat) :
    ∀ e ∈ bodies B n x y d (fun _ => .const 0), e.eval (fun _ => 0) ≡ 0 [ZMOD 2013265921] := by
  intro e he
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp he
  simp [limbBody, EmittedExpr.eval]

#assert_all_clean [modular_limb_sound, chain_identity, value_nonneg, bodies_sound,
  top_borrow_falsifier, zero_chain_holds]
/-- info: 'Dregg2.Circuit.Emit.BorrowChainEmit.modular_limb_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms modular_limb_sound
/-- info: 'Dregg2.Circuit.Emit.BorrowChainEmit.bodies_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bodies_sound
end Dregg2.Circuit.Emit.BorrowChainEmit

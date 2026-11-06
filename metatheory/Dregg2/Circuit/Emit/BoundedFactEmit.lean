/-
# BoundedFactEmit — reusable range and fact-opening AIR generators

Ranges are authored once, with integer semantics lifted from BabyBear congruences.
Fact sites absorb exactly five padded predicate/term slots plus the hash_fact domain
marker and delimiter, and reuse the verified full-lane chip lookup interface.
-/
import Dregg2.Circuit.Emit.FieldDeltaRangeEmit
namespace Dregg2.Circuit.Emit.BoundedFactEmit
open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.FieldDeltaRangeEmit (Canon eq_of_modEq_canon)
set_option autoImplicit false

def sub (x y : EmittedExpr) : EmittedExpr := .add x (.mul (.const (-1)) y)
def boolean (c : Nat) : EmittedExpr := .mul (.var c) (sub (.var c) (.const 1))
def recompose (bits value base : Nat) : EmittedExpr :=
  (List.range bits).foldl
    (fun acc j => sub acc (.mul (.const ((2 : Int) ^ j)) (.var (base + j)))) (.var value)
def rangeBodies (bits value base : Nat) : List EmittedExpr :=
  (List.range bits).map (fun j => boolean (base + j)) ++ [recompose bits value base]

theorem boolean_forces {a : Assignment} {c : Nat}
    (h : (boolean c).eval a ≡ 0 [ZMOD 2013265921]) (hc : Canon (a c)) :
    a c = 0 ∨ a c = 1 := by
  have hd : (2013265921 : Int) ∣ a c * (a c - 1) := by
    apply Int.modEq_zero_iff_dvd.mp
    simpa [boolean, sub, EmittedExpr.eval, sub_eq_add_neg] using h
  obtain ⟨h0, h1⟩ := hc
  rcases Dregg2.Circuit.Emit.EffectVmEmitTransfer.pPrimeInt.dvd_mul.mp hd with hd | hd
  · obtain ⟨k, hk⟩ := hd; left; omega
  · obtain ⟨k, hk⟩ := hd; right; omega

theorem recompose_fold_eval (a : Assignment) (base : Nat) :
    ∀ (l : List Nat) (e : EmittedExpr),
    (l.foldl (fun acc j => sub acc (.mul (.const ((2 : Int) ^ j))
      (.var (base + j)))) e).eval a =
      e.eval a - (l.map (fun j => (2 : Int) ^ j * a (base + j))).sum := by
  intro l
  induction l with
  | nil => intro e; simp
  | cons x xs ih =>
    intro e
    rw [List.foldl_cons, ih]
    simp only [List.map_cons, List.sum_cons, sub, EmittedExpr.eval]
    ring

theorem bitSum_bounds (a : Assignment) (base : Nat) :
    ∀ n, (∀ j < n, a (base + j) = 0 ∨ a (base + j) = 1) →
      0 ≤ ((List.range n).map (fun j => (2 : Int) ^ j * a (base + j))).sum ∧
      ((List.range n).map (fun j => (2 : Int) ^ j * a (base + j))).sum < 2 ^ n := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ k ih =>
    intro h
    obtain ⟨h0, h1⟩ := ih (fun j hj => h j (Nat.lt_succ_of_lt hj))
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    have hp : (0 : Int) ≤ 2 ^ k := by positivity
    have he : (2 : Int) ^ k.succ = 2 ^ k + 2 ^ k := by rw [pow_succ]; ring
    rcases h k (Nat.lt_succ_self k) with h | h <;> rw [h] <;> constructor <;> nlinarith

/-- Generic, layout-independent soundness of the emitted range block. -/
theorem rangeBodies_sound (a : Assignment) (bits value base : Nat)
    (hfit : (2 : Int) ^ bits < 2013265921)
    (hcanon : ∀ c, Canon (a c))
    (h : ∀ e ∈ rangeBodies bits value base, e.eval a ≡ 0 [ZMOD 2013265921]) :
    0 ≤ a value ∧ a value < 2 ^ bits := by
  have hb : ∀ j < bits, a (base + j) = 0 ∨ a (base + j) = 1 := by
    intro j hj
    apply boolean_forces (h _ ?_) (hcanon _)
    simp only [rangeBodies, List.mem_append, List.mem_map, List.mem_range]
    exact Or.inl ⟨j, hj, rfl⟩
  have hr := h (recompose bits value base) (by simp [rangeBodies])
  have he := recompose_fold_eval a base (List.range bits) (.var value)
  change (recompose bits value base).eval a = _ at he
  rw [he] at hr
  simp only [EmittedExpr.eval] at hr
  obtain ⟨hs0, hs1⟩ := bitSum_bounds a base bits hb
  have hm : a value ≡ ((List.range bits).map
      (fun j => (2 : Int) ^ j * a (base + j))).sum [ZMOD 2013265921] := by
    obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp hr
    exact Int.modEq_iff_dvd.mpr ⟨-k, by linear_combination -hk⟩
  have heq := eq_of_modEq_canon hm (hcanon value) ⟨hs0, lt_trans hs1 hfit⟩
  exact ⟨by rw [heq]; exact hs0, by rw [heq]; exact hs1⟩


/-- Decompose `value - offset`; the endpoint is `offset + 2^bits - 1`. -/
def recomposeOffset (bits value base : Nat) (offset : Int) : EmittedExpr :=
  (List.range bits).foldl
    (fun acc j => sub acc (.mul (.const ((2 : Int) ^ j)) (.var (base + j))))
    (sub (.var value) (.const offset))
def rangeBodiesOffset (bits value base : Nat) (offset : Int) : List EmittedExpr :=
  (List.range bits).map (fun j => boolean (base + j)) ++
    [recomposeOffset bits value base offset]

theorem offset_range_sound (a : Assignment) (bits value base : Nat) (offset : Int)
    (ho : 0 ≤ offset) (hfit : offset + (2 : Int)^bits ≤ 2013265921)
    (hcanon : ∀ c, Canon (a c))
    (h : ∀ e ∈ rangeBodiesOffset bits value base offset,
      e.eval a ≡ 0 [ZMOD 2013265921]) :
    offset ≤ a value ∧ a value < offset + 2^bits := by
  have hb : ∀ j < bits, a (base + j) = 0 ∨ a (base + j) = 1 := by
    intro j hj
    apply boolean_forces (h _ ?_) (hcanon _)
    simp only [rangeBodiesOffset, List.mem_append, List.mem_map, List.mem_range]
    exact Or.inl ⟨j, hj, rfl⟩
  have hr := h (recomposeOffset bits value base offset) (by simp [rangeBodiesOffset])
  have he := recompose_fold_eval a base (List.range bits) (sub (.var value) (.const offset))
  change (recomposeOffset bits value base offset).eval a = _ at he
  rw [he] at hr
  simp only [sub, EmittedExpr.eval] at hr
  obtain ⟨hs0, hs1⟩ := bitSum_bounds a base bits hb
  have hm : a value ≡ offset + ((List.range bits).map
      (fun j => (2 : Int) ^ j * a (base + j))).sum [ZMOD 2013265921] := by
    obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp hr
    exact Int.modEq_iff_dvd.mpr ⟨-k, by linear_combination -hk⟩
  have heq := eq_of_modEq_canon hm (hcanon value) ⟨by omega, by omega⟩
  constructor <;> omega

/-- Predicate and up to four terms, explicitly padded by the caller. -/
abbrev FactInputs := Fin 5 → EmittedExpr
def factAbsorb (inputs : FactInputs) : List EmittedExpr :=
  [inputs 0, inputs 1, inputs 2, inputs 3, inputs 4, .const 64207, .const 1]
def factSite (inputs : FactInputs) (output lanes : Nat) : VmConstraint2 :=
  .lookup ⟨.poseidon2, chipLookupTupleN (factAbsorb inputs)
    (output :: (List.range 7).map (fun j => lanes + j)) (by change ChipArityAdmitted 7; decide)⟩

/-- Every output lane is supplied by a sound chip table; in particular its head. -/
theorem factSite_sound (permOut : List Int → List Int) (tf : TraceFamily)
    (hchip : ChipTableSoundN permOut (tf .poseidon2))
    (env : VmRowEnv) (hash : List Int → Int) (first last : Bool)
    (inputs : FactInputs) (output lanes : Nat)
    (h : (factSite inputs output lanes).holdsAt hash tf env first last) :
    env.loc output = (permOut ((factAbsorb inputs).map (·.eval env.loc))).headD 0 := by
  have hh := chip_lookup_sound_N permOut (tf .poseidon2) hchip env.loc
    (factAbsorb inputs) (output :: (List.range 7).map (fun j => lanes + j))
    (by change ChipArityAdmitted 7; decide) h
  have := congrArg (fun xs : List Int => xs.headD 0) hh
  simpa using this

/-- info: 'Dregg2.Circuit.Emit.BoundedFactEmit.boolean_forces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms boolean_forces
/-- info: 'Dregg2.Circuit.Emit.BoundedFactEmit.recompose_fold_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms recompose_fold_eval
/-- info: 'Dregg2.Circuit.Emit.BoundedFactEmit.bitSum_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bitSum_bounds
/-- info: 'Dregg2.Circuit.Emit.BoundedFactEmit.rangeBodies_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rangeBodies_sound
/-- info: 'Dregg2.Circuit.Emit.BoundedFactEmit.offset_range_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms offset_range_sound
/-- info: 'Dregg2.Circuit.Emit.BoundedFactEmit.factSite_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms factSite_sound
end Dregg2.Circuit.Emit.BoundedFactEmit

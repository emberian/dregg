/-
# Dregg2.Exec.RecordCircuit — the circuit compiler over records (THE PRIZE).

`Exec/Value.lean` flattens a record to a fixed-width field vector (`flatten_width`);
`Exec/Program.lean` is the `CellProgram`/`StateConstraint` structure-map reading named fields.
This module is the payoff: **compile `(Schema, CellProgram) → ConstraintSystem`** over the
flattened wires and PROVE the bridge

    satisfied (compile schema prog) (encodeTransition …) ↔ prog.admits method old new

so checking the AIR over a *structured record* is the same as the verified admissibility filter.
Very little ZK tooling works over records; this makes it sound by construction.

## The honest part — order comparisons via bit-decomposition (no primitive seam)
Arithmetic constraints (`fieldEquals`/`fieldDelta`/`sumEquals`/`sumEqualsAcross`/`fieldLeField`)
compile to clean field gates. **Order comparisons (`≤`/`<`/`monotonic`/…) are NOT native field
operations** — each compiles to an explicit **bit-decomposition range gadget**: to prove a value
`v` is in `[0, 2ⁿ)`, introduce `n` bit-wires `bᵢ` with booleanity gates `bᵢ·(1-bᵢ)=0` and a
recomposition gate `v = Σ bᵢ·2ⁱ`. This is ~`n` gates per comparison — the *real* ZK-over-records
cost, made explicit and **fully proven** (no assumed/primitive soundness, unlike the digest seam
in `Circuit.lean`).

This file (Part 1) builds and proves that range-gadget core: `bitsToInt`, `range_sound`
(booleanity ⇒ in range), `range_complete` (in range ⇒ bits exist). The constraint compiler and
the bridge theorem ride on top of it.
-/
import Mathlib.Tactic

namespace Dregg2.Exec.RecordCircuit

/-! ## The bit-decomposition range gadget (the pure math the gates encode). -/

/-- Little-endian recomposition of a bit list: `Σ bᵢ·2ⁱ`. The recomposition gate the circuit
emits constrains the value wire to equal this. -/
def bitsToInt : List Int → Int
  | []        => 0
  | b :: rest => b + 2 * bitsToInt rest

/-- Booleanity: every entry is `0` or `1` (what the per-bit gate `bᵢ·(1-bᵢ)=0` enforces). -/
def Boolean (bits : List Int) : Prop := ∀ b ∈ bits, b = 0 ∨ b = 1

/-- **`range_sound` (PROVED) — the gate ⇒ range direction.** If the bits are boolean, their
recomposition lies in `[0, 2^(#bits))`. This is what makes a satisfied range gadget *prove* a
comparison: a value with a valid `n`-bit decomposition is provably in `[0, 2ⁿ)`. -/
theorem range_sound : ∀ (bits : List Int), Boolean bits →
    0 ≤ bitsToInt bits ∧ bitsToInt bits < 2 ^ bits.length
  | [],        _ => by simp [bitsToInt]
  | b :: rest, h => by
      have hb : b = 0 ∨ b = 1 := h b (by simp)
      have hrest : Boolean rest := fun x hx => h x (List.mem_cons_of_mem _ hx)
      obtain ⟨hr0, hr1⟩ := range_sound rest hrest
      have h2 : (2 : ℤ) ^ (rest.length + 1) = 2 ^ rest.length * 2 := by rw [pow_succ]
      simp only [bitsToInt, List.length_cons]
      rcases hb with rfl | rfl <;> omega

/-- **`range_complete` (PROVED) — the range ⇒ gate direction.** Every `v ∈ [0, 2ⁿ)` has an
`n`-bit boolean decomposition. This is what makes the range gadget *satisfiable* whenever the
comparison really holds — the completeness half of the bridge. -/
theorem range_complete : ∀ (n : Nat) (v : Int), 0 ≤ v → v < 2 ^ n →
    ∃ bits : List Int, bits.length = n ∧ Boolean bits ∧ bitsToInt bits = v
  | 0,     v, h0, h1 => by
      simp only [pow_zero] at h1
      have hv : v = 0 := by omega
      exact ⟨[], rfl, by intro b hb; simp at hb, by simp [bitsToInt, hv]⟩
  | n + 1, v, h0, h1 => by
      have ht : (2 : ℤ) ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
      have hbit : v % 2 = 0 ∨ v % 2 = 1 := Int.emod_two_eq_zero_or_one v
      have hv0 : 0 ≤ v / 2 := Int.ediv_nonneg h0 (by norm_num)
      have hv1 : v / 2 < 2 ^ n := by
        have hlt : v < 2 * 2 ^ n := by rw [← ht]; exact h1
        omega
      obtain ⟨bits, hlen, hbool, hrec⟩ := range_complete n (v / 2) hv0 hv1
      refine ⟨v % 2 :: bits, by simp [hlen], ?_, ?_⟩
      · intro b hb'
        rcases List.mem_cons.mp hb' with rfl | hmem
        · exact hbit
        · exact hbool b hmem
      · simp only [bitsToInt, hrec]
        omega

/-- **`range_iff` (PROVED) — the gadget is sound ∧ complete.** A value is in `[0, 2ⁿ)` *iff* an
`n`-bit boolean decomposition of it exists. This single equivalence is what the constraint
compiler turns each `≤`/`<`/`monotonic` gate into, with both bridge directions free. -/
theorem range_iff (n : Nat) (v : Int) :
    (0 ≤ v ∧ v < 2 ^ n) ↔ ∃ bits : List Int, bits.length = n ∧ Boolean bits ∧ bitsToInt bits = v := by
  constructor
  · rintro ⟨h0, h1⟩; exact range_complete n v h0 h1
  · rintro ⟨bits, hlen, hbool, hrec⟩
    obtain ⟨hs0, hs1⟩ := range_sound bits hbool
    rw [hrec] at hs0 hs1
    rw [hlen] at hs1
    exact ⟨hs0, hs1⟩

/-- A comparison `a ≤ b` (for values known to fit in `n` bits) reduces to "`b - a` has an
`n`-bit boolean decomposition" — the form the circuit's `≤` gadget proves. PROVED. -/
theorem le_iff_range (n : Nat) (a b : Int) (ha : a ≤ b) (hb : b - a < 2 ^ n) :
    ∃ bits : List Int, bits.length = n ∧ Boolean bits ∧ bitsToInt bits = b - a :=
  range_complete n (b - a) (by omega) hb

/-- And conversely: a valid `n`-bit decomposition of `b - a` proves `a ≤ b`. PROVED — this is
the soundness of the `≤` gadget (a satisfying witness forces the comparison). -/
theorem range_proves_le (a b : Int) (bits : List Int) (hbool : Boolean bits)
    (hrec : bitsToInt bits = b - a) : a ≤ b := by
  have := (range_sound bits hbool).1
  rw [hrec] at this
  omega

end Dregg2.Exec.RecordCircuit

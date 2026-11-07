/-
# Certified union of byte tables

The existing `TableDfa` bridge proves fold faithfulness; `Compile.Certified` carries exactly
that language agreement for printable byte tables. Compose those tables directly instead of
asking derivative exploration to rediscover the product. `Factor.closedB` supplies the bounded
state invariant needed by the dense row numbering. Every returned table carries its proof.

[READ] This reuses `Factor.closedB`, `Factor.closed_run`, `PredRE.derives_alt`, and the existing
`Certified` API; it does not introduce a second semantics or unchecked table importer. The
product has `A.n * B.n` rows and 256 columns; subsequent checked minimization may remove
unreachable/equivalent rows. The construction itself does not promise a minimal table.

Reproduce the named falsifiers and exact axiom pins on warm dependencies:
`cd metatheory && lake env lean Dregg2/Policy/Union.lean`.
[MEASURED] The reference product has six rows, with unequal component sizes three and two.
-/
import Dregg2.Policy.Factor

namespace Dregg2.Policy

open Dregg2.Crypto.Deriv
open Dregg2.Crypto.Deriv.PredRE

set_option autoImplicit false

/-- Dense product rows, accepting when either component accepts. -/
def Table.union (A B : Table) : Table where
  n := A.n * B.n
  start := A.start * B.n + B.start
  step s b := A.step (s / B.n) b * B.n + B.step (s % B.n) b
  acc s := A.acc (s / B.n) || B.acc (s % B.n)

theorem union_decode (n p q : Nat) (hq : q < n) :
    (p * n + q) / n = p ∧ (p * n + q) % n = q := by
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.zero_lt_of_lt hq),
      Nat.div_eq_of_lt hq, Nat.zero_add]
  · simp [Nat.add_mod, Nat.mod_eq_of_lt hq]

theorem union_encode_lt {m n p q : Nat} (hp : p < m) (hq : q < n) :
    p * n + q < m * n := by
  calc
    p * n + q < p * n + n := Nat.add_lt_add_left hq _
    _ = (p + 1) * n := by simp [Nat.add_mul]
    _ ≤ m * n := Nat.mul_le_mul_right n hp

/-- Product execution projects to both component executions, for every byte word. -/
theorem union_run (A B : Table) (hB : closedB B = true) :
    ∀ (w : List Nat), w.all (· < 256) = true → ∀ p q, q < B.n →
    (A.union B).run (p * B.n + q) w = A.run p w * B.n + B.run q w := by
  have hstep : ∀ q, q < B.n → ∀ b, b < 256 → B.step q b < B.n := by
    simp only [closedB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.mem_range] at hB
    exact hB.2
  intro w
  induction w with
  | nil => intros; rfl
  | cons b w ih =>
    intro hw p q hq
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hw
    have hd := union_decode B.n p q hq
    change (A.union B).run ((A.union B).step (p * B.n + q) b) w =
      A.run (A.step p b) w * B.n + B.run (B.step q b) w
    simp only [Table.union, hd.1, hd.2]
    exact ih hw.2 _ _ (hstep q hq b hw.1)

theorem union_closed (A B : Table) (hA : closedB A = true) (hB : closedB B = true) :
    closedB (A.union B) = true := by
  simp only [closedB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hA hB ⊢
  refine ⟨union_encode_lt hA.1 hB.1, ?_⟩
  intro s hs b hb
  have hn : 0 < B.n := Nat.zero_lt_of_lt hB.1
  have hp : s / B.n < A.n := (Nat.div_lt_iff_lt_mul hn).mpr hs
  have hq : s % B.n < B.n := Nat.mod_lt _ hn
  exact union_encode_lt (hA.2 _ hp _ hb) (hB.2 _ hq _ hb)

/-- Union's verdict is the disjunction of its component verdicts on the whole word. -/
theorem union_verdict (A B : Table) (hB : closedB B = true) (w : List Nat)
    (hw : w.all (· < 256) = true) :
    (A.union B).acc ((A.union B).run (A.union B).start w) =
      (A.acc (A.run A.start w) || B.acc (B.run B.start w)) := by
  have hstart : B.start < B.n := by
    simp only [closedB, Bool.and_eq_true, decide_eq_true_eq] at hB
    exact hB.1
  change (A.union B).acc ((A.union B).run (A.start * B.n + B.start) w) = _
  rw [union_run A B hB w hw _ _ hstart]
  have hd := union_decode B.n (A.run A.start w) (B.run B.start w)
    (closed_run hB w hw _ hstart)
  simp only [Table.union, hd.1, hd.2]

/-- Compose two certified tables without repeating derivative exploration of their union. -/
def Certified.union {R S : PredRE} (a : Certified R) (b : Certified S)
    (_ha : closedB a.t = true) (hb : closedB b.t = true) : Certified (.alt R S) where
  t := a.t.union b.t
  hdec w hw := by
    rw [union_verdict a.t b.t hb w hw, derives_alt, Bool.or_eq_true, Bool.or_eq_true]
    exact or_congr (a.hdec w hw) (b.hdec w hw)

/-- Refuse malformed bounds rather than silently using an invalid dense-row decoder. -/
def certifyUnion {R S : PredRE} (a : Certified R) (b : Certified S) :
    Except String (Certified (.alt R S)) :=
  if ha : closedB a.t = true then
    if hb : closedB b.t = true then .ok (a.union b ha hb)
    else .error "union right table is not closed on bytes"
  else .error "union left table is not closed on bytes"

theorem certifyUnion_ok {R S : PredRE} (a : Certified R) (b : Certified S)
    (ha : closedB a.t = true) (hb : closedB b.t = true) :
    certifyUnion a b = .ok (a.union b ha hb) := by simp [certifyUnion, ha, hb]

/-- The certified constructor also preserves the finite table bounds. -/
theorem Certified.union_closed {R S : PredRE} (a : Certified R) (b : Certified S)
    (ha : closedB a.t = true) (hb : closedB b.t = true) :
    closedB (a.union b ha hb).t = true := Dregg2.Policy.union_closed a.t b.t ha hb

namespace UnionReference

set_option maxRecDepth 4096

/-- A nonconstant table for exactly one byte; dead row 0, start row 1, accepting row 2. -/
def oneByteTable : Table := ⟨3, fun s _ => if s == 1 then 2 else 0, (· == 2), 1⟩
/-- Exactly the empty word, with a different row count to exercise the product decoder. -/
def epsilonTable : Table := ⟨2, fun _ _ => 0, (· == 1), 1⟩

theorem run_dead (t : Table) (h : ∀ b, t.step 0 b = 0) (w : List Nat) :
    t.run 0 w = 0 := by
  induction w with
  | nil => rfl
  | cons b w ih => change t.run (t.step 0 b) w = 0; rw [h]; exact ih

def oneByte : Certified PredRE.any where
  t := oneByteTable
  hdec w _ := by
    cases w with
    | nil => decide
    | cons b w =>
      cases w with
      | nil => rfl
      | cons c w =>
        change oneByteTable.acc (oneByteTable.run 0 w) = true ↔ derives (w.map byteFrame) bot = true
        rw [run_dead oneByteTable (fun _ => rfl), derives_bot]
        decide

def epsilon : Certified .ε where
  t := epsilonTable
  hdec w _ := by
    cases w with
    | nil => decide
    | cons b w =>
      change epsilonTable.acc (epsilonTable.run 0 w) = true ↔ derives (w.map byteFrame) bot = true
      rw [run_dead epsilonTable (fun _ => rfl), derives_bot]
      decide

theorem component_bounds : closedB oneByte.t = true ∧ closedB epsilon.t = true := by decide

def either : Certified (.alt PredRE.any .ε) :=
  oneByte.union epsilon component_bounds.1 component_bounds.2

/-- Right-only, left-only and neither: replacing union by either projection or conjunction fails. -/
theorem union_choices :
    oneByte.t.acc (oneByte.t.run oneByte.t.start []) = false ∧
    either.t.acc (either.t.run either.t.start []) = true ∧
    epsilon.t.acc (epsilon.t.run epsilon.t.start [255]) = false ∧
    either.t.acc (either.t.run either.t.start [255]) = true ∧
    either.t.acc (either.t.run either.t.start [0, 255]) = false := by decide

/-- The real constructor inhabits all bounds and byte-language premises, for every word. -/
theorem either_decides (w : List Nat) (hw : w.all (· < 256) = true) :
    either.t.acc (either.t.run either.t.start w) = true ↔
      derives (w.map byteFrame) (.alt PredRE.any .ε) = true := either.hdec w hw

theorem product_counts : either.t.n = 6 ∧ either.t.start = 3 ∧ closedB either.t = true := by decide

/-- Language certification alone does not imply finite row bounds: `n` is absent from `hdec`. -/
def badBounds : Certified .ε := ⟨{ epsilonTable with n := 0 }, epsilon.hdec⟩

theorem malformed_refused :
    certifyUnion badBounds oneByte = .error "union left table is not closed on bytes" ∧
    certifyUnion oneByte badBounds = .error "union right table is not closed on bytes" := by
  constructor <;> rfl

end UnionReference

#assert_all_clean [union_decode, union_encode_lt, union_run, union_closed, union_verdict, certifyUnion_ok,
  Certified.union_closed, UnionReference.run_dead, UnionReference.component_bounds,
  UnionReference.union_choices, UnionReference.either_decides, UnionReference.product_counts,
  UnionReference.malformed_refused]

/-- info: 'Dregg2.Policy.union_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms union_run
/-- info: 'Dregg2.Policy.union_closed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms union_closed
/-- info: 'Dregg2.Policy.union_verdict' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms union_verdict
/-- info: 'Dregg2.Policy.Certified.union' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Certified.union
/-- info: 'Dregg2.Policy.UnionReference.either_decides' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms UnionReference.either_decides
/-- info: 'Dregg2.Policy.UnionReference.union_choices' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms UnionReference.union_choices
/-- info: 'Dregg2.Policy.UnionReference.malformed_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms UnionReference.malformed_refused

end Dregg2.Policy

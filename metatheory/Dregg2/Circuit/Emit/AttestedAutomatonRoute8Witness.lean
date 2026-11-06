/- A concrete accepted full-width routed weld and a record-substitution falsifier.
The hash here is a transparent eight-output reference function, not Poseidon2. -/
import Dregg2.Circuit.Emit.AttestedAutomatonRoute8
namespace Dregg2.Circuit.Emit.AttestedAutomatonRoute8Witness
open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.Emit.AttestedAutomatonRoute8
open Dregg2.Circuit.Emit.AttestedAutomatonBound
open Dregg2.Circuit.Emit.AttestedAutomatonWeld8
open Dregg2.Circuit.Emit.AttestedAutomatonLanes8
open Dregg2.Circuit.Emit.AttestedAutomatonEmit (attContinuity attB1 attB2 ASYM ASTATES)
open Dregg2.Circuit.Emit.DfaRoutingTableEmit (CURRENT SYMBOL NEXT PI_INITIAL PI_FINAL)
open Dregg2.Circuit.MapMerkleRoot (zeroDigest8)
open Dregg2.Substrate
set_option autoImplicit false

def hash8 (input : List ℤ) : List ℤ := [input.getD 3 0 % 2013265921, 0, 0, 0, 0, 0, 0, 0]
theorem hash8_width (input : List ℤ) : (hash8 input).length = 8 := rfl

def row : Assignment := fun k => if k = 1 ∨ k = 19 ∨ k = 27 then 1 else 0
def pubvals : Assignment := fun k => if k = 10 ∨ k = 18 then 1 else 0

def input : List ℤ := [1464159288, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def tables : TraceFamily := fun tid =>
  if tid = .poseidon2 then [chipRowN hash8 input]
  else if tid = .mapOps then [weldMapRow8 row]
  else if tid = WELD_TID_RANGE15 then rangeRows 15
  else if tid = WELD_TID_RANGE1 then rangeRows 1 else []
def witness : VmTrace := { rows := [row], pub := pubvals, tf := tables }

theorem witness_canonical : RouteChain8Refine.Canonical witness := by
  constructor
  · intro i hi j
    have hz : i = 0 := by change i < 1 at hi; omega
    subst i
    change 0 ≤ row j ∧ row j < 2013265921
    unfold row
    split_ifs <;> norm_num
  · intro j
    change 0 ≤ pubvals j ∧ pubvals j < 2013265921
    unfold pubvals
    split_ifs <;> norm_num

theorem witness_chip_sound : ChipTableSoundN hash8 (witness.tf .poseidon2) := by
  intro r hr
  have he : r = chipRowN hash8 input := List.mem_singleton.mp hr
  subst r
  exact ⟨input, by decide, rfl⟩

theorem witness_ranges : WeldRangeTablesFaithful witness.tf := by
  constructor <;> simp [witness, tables, WELD_TID_RANGE15, WELD_TID_RANGE1]

theorem row_root : weldOp.rootAt row = zeroDigest8 := by
  funext l
  fin_cases l <;> rfl

theorem row_opens : weldOp.holdsAt8 constChip (envAt witness 0) := by
  intro _
  refine ⟨?_, rfl⟩
  change Dregg2.Circuit.MapMerkleRoot.opensToMerkle8 constChip MAP_TREE_DEPTH
    (weldOp.rootAt row) 1 (some 0)
  rw [row_root, ← autoRoot8_constChip zeroD]
  exact autoRoot8_opens constChip zeroD 0 1 (by decide) (by decide)

private theorem base_rows (name : String) :
    ∀ c ∈ (weldDesc name).constraints,
      c.holdsAt8 constChip (fun _ => 0) witness.tf (envAt witness 0) true true := by
  intro c hc
  simp only [weldDesc, List.mem_cons] at hc
  rcases hc with rfl | rfl | rfl | rfl | hc
  · exact row_opens
  · simp [attContinuity, VmConstraint2.holdsAt8, VmConstraint2.holdsAt, WindowConstraint.holdsAt]
  · intro _; exact Int.ModEq.refl _
  · intro _; exact Int.ModEq.refl _
  · rcases weldTail_classify hc with ⟨l, rfl | rfl⟩ | rfl | rfl
    · simp [weldRootConst, VmConstraint2.holdsAt8, VmConstraint2.holdsAt, WindowConstraint.holdsAt]
    · intro _; fin_cases l <;> exact Int.ModEq.refl _
    · change [(EmittedExpr.var CURRENT).eval (envAt witness 0).loc] ∈ witness.tf WELD_TID_RANGE15
      rw [witness_ranges.1, range_row_mem_iff]
      norm_num [EmittedExpr.eval, envAt, witness, row, CURRENT]
    · change [(EmittedExpr.var SYMBOL).eval (envAt witness 0).loc] ∈ witness.tf WELD_TID_RANGE1
      rw [witness_ranges.2, range_row_mem_iff]
      norm_num [EmittedExpr.eval, envAt, witness, row, SYMBOL]

private theorem route_rows : RouteChain8Refine.RowsHold weldRouteConfig (fun _ => 0) witness := by
  intro i hi c hc
  have hz : i = 0 := by change i < 1 at hi; omega
  subst i
  simp only [RouteChain8.constraints, RouteChain8.lanes, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
  | exact List.mem_singleton_self _
  | (intro _; exact Int.ModEq.refl _)
  | simp [RouteChain8.copy, RouteChain8.indexStep, VmConstraint2.holdsAt, WindowConstraint.holdsAt,
      witness]

/-- All full-width map, route, range and boundary obligations are jointly satisfied. -/
theorem witness_satisfies (name : String) :
    Satisfied2Lanes8 constChip (fun _ => 0) (weldBoundDesc name)
      (fun _ => 0) (fun _ => (0,0)) [] witness := by
  have hm : memLog (weldBoundDesc name) witness = [] := by
    simp [weldBoundDesc, memLog, RouteChain8.memOps_decorate, weld_memOps]
  have hp : mapLog8 (weldBoundDesc name) witness = [weldMapRow8 row] := by
    simp only [weldBoundDesc, mapLog8, RouteChain8.mapOps_decorate]
    exact weld_mapLog8 name witness
  refine {
    rowConstraints := ?_
    rowHashes := by intro i hi; trivial
    rowRanges := by intro i hi r hr; exact False.elim (List.not_mem_nil hr)
    memAddrsNodup := List.nodup_nil
    memClosed := by rw [hm]; simp
    memDisciplined := by rw [hm]; trivial
    memBalanced := by rw [hm]; exact memCheck_nil _ _
    memTableFaithful := by rw [hm]; rfl
    mapTableFaithful8 := by rw [hp]; rfl
    publicTablesFaithful := ?_
    publicLookupBalanced := ?_ }
  · intro i hi c hc
    have hz : i = 0 := by change i < 1 at hi; omega
    subst i
    rcases List.mem_append.mp hc with hc | hc
    · exact base_rows name c hc
    · have hh := route_rows 0 hi c hc
      have hn : ∀ m, c ≠ .mapOp m := by
        intro m he
        subst c
        simp [RouteChain8.constraints, RouteChain8.lanes, RouteChain8.chip, RouteChain8.copy,
          RouteChain8.seedPin, RouteChain8.outputPin, RouteChain8.indexFirst, RouteChain8.indexStep,
          RouteChain8.indexLast, weldRouteConfig] at hc
      exact VmConstraint2.holdsAt8_of_not_mapOp constChip (fun _ => 0) _ _ _ _ c hn hh
  · intro td htd
    simp only [weldBoundDesc, RouteChain8.decorate, weldDesc, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at htd
    rcases htd with rfl | rfl | rfl | rfl <;> trivial
  · intro td htd
    simp only [weldBoundDesc, RouteChain8.decorate, weldDesc, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at htd
    rcases htd with rfl | rfl | rfl | rfl <;> trivial

theorem hash8_canonical (xs : List ℤ) : CanonicalValues (hash8 xs) := by
  intro x hx
  simp only [hash8, List.mem_cons, List.not_mem_nil, or_false, or_self] at hx
  rcases hx with rfl | rfl
  · exact ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩
  · norm_num

theorem witness_pubroot : pubRoot witness = zeroDigest8 := by
  funext l
  fin_cases l <;> rfl

theorem witness_commits : CommitsAutomaton8By constChip (autoHeapW zeroD) (pubRoot witness) zeroD := by
  rw [witness_pubroot, ← autoRoot8_constChip zeroD]
  exact autoRoot8_commits constChip zeroD

/-- The supplied per-row opening family is concrete, with the committing automaton heap. -/
def witness_openings : RowHeaps constChip witness where
  heap := fun _ => autoHeapW zeroD
  sorted := fun _ => autoHeapW_sorted zeroD
  length := fun _ => autoHeapW_length zeroD
  root := fun _ => witness_commits.2.2.1
  opening := by
    rintro ⟨i, hi⟩
    have hz : i = 0 := by change i < 1 at hi; omega
    subst i
    exact autoHeapW_get zeroD 0 1 (by decide) (by decide)

theorem witness_payload : RouteChain8Refine.payloads weldRouteConfig witness =
    recordPayloads zeroD 0 0 [1] := rfl

theorem witness_record_canonical :
    ∀ p ∈ recordPayloads zeroD 0 0 [1], CanonicalValues p := by
  intro p hp
  have he : p = [1464159288,1,0,1,0] := List.mem_singleton.mp hp
  subst p
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem witness_record_opens :
    RouteChain8Refine.publicRoute weldRouteConfig witness = recordCommit hash8 witness zeroD 0 [1] := by
  decide

theorem witness_length : witness.pub (RouteChain8.lengthPi weldRouteConfig) = (([1] : List Nat).length : ℤ) := rfl

/-- The content-bound theorem fires on one jointly inhabited accepted witness. -/
theorem whole_theorem_inhabited (name : String) :
    (readWord witness = [1] ∧
      (0 = Dregg2.Crypto.DfaAcceptanceAir.classifyFrom zeroD 0 [1] ∨
        RowCollision constChip witness zeroD witness_openings (autoHeapW zeroD))) ∨
      RecordCollision hash8 witness zeroD 0 [1] :=
  strongAccepts_sound hash8 zeroD 0 0 [1]
    ⟨⟨witness_satisfies name, rfl, rfl⟩, witness_record_opens, witness_length⟩
    witness_openings witness_ranges witness_canonical (by simp [witness]) (by decide)
    hash8_width hash8_canonical witness_chip_sound zeroD_step witness_commits
    (by decide) (by decide) witness_record_canonical

/-- Both residuals are false on this actual accepted witness, even though its map chip is constant. -/
theorem witness_no_residual :
    ¬ RowCollision constChip witness zeroD witness_openings (autoHeapW zeroD) ∧
    ¬ RecordCollision hash8 witness zeroD 0 [1] := by
  constructor
  · rintro ⟨i, hbad, _⟩
    have hz : i.val = 0 := by have hi := i.isLt; change i.val < 1 at hi; omega
    have hi : i = ⟨0, by decide⟩ := Fin.ext hz
    subst i
    exact hbad rfl
  · exact honest_record_no_collision hash8 witness zeroD 0 [1] witness_payload

/-- Concrete specialization of the generic verifier's weak relation on one fixed proof/statement. -/
def WeakAccepts (name : String) (record : List Nat) : Prop :=
  AttestedAutomatonRoute8.WeakAccepts constChip (fun _ => 0) name
    (fun _ => 0) (fun _ => (0,0)) [] witness 0 0 record

/-- The SAME proof/statement, with the supplied record's route and length checked as well. -/
def StrongAccepts (name : String) (record : List Nat) : Prop :=
  AttestedAutomatonRoute8.StrongAccepts constChip (fun _ => 0) name
    (fun _ => 0) (fun _ => (0,0)) [] witness hash8 zeroD 0 0 record

/-- The stronger verifier is itself inhabited, using the actual accepted proof and honest record. -/
theorem honest_strong_accepts (name : String) : StrongAccepts name [1] :=
  ⟨⟨witness_satisfies name, rfl, rfl⟩, witness_record_opens, witness_length⟩

/-- The wrong record fails precisely the route-opening comparison. -/
theorem substitution_route_mismatch :
    RouteChain8Refine.publicRoute weldRouteConfig witness ≠ recordCommit hash8 witness zeroD 0 [0] := by
  decide

/-- The same accepted trace and public endpoints refuse the substituted record under strong
acceptance; the relation is the one consumed by `strongAccepts_sound`. -/
theorem strong_refuses_substitution (name : String) : ¬ StrongAccepts name [0] := by
  intro h
  exact substitution_route_mismatch h.2.1

/-- The weak verifier accepts the substituted record at the SAME proof and public endpoints. -/
theorem weak_accepts_substitution (name : String) : WeakAccepts name [0] :=
  ⟨witness_satisfies name, rfl, rfl⟩

/-- Isolated weak-accepts/strong-refuses separation, with proof, statement and record held fixed. -/
theorem substitution_separation (name : String) :
    WeakAccepts name [0] ∧ ¬ StrongAccepts name [0] :=
  ⟨weak_accepts_substitution name, strong_refuses_substitution name⟩

/-- info: 'Dregg2.Circuit.Emit.AttestedAutomatonRoute8Witness.witness_satisfies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms witness_satisfies
/-- info: 'Dregg2.Circuit.Emit.AttestedAutomatonRoute8Witness.whole_theorem_inhabited' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms whole_theorem_inhabited
/-- info: 'Dregg2.Circuit.Emit.AttestedAutomatonRoute8Witness.witness_no_residual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms witness_no_residual
/-- info: 'Dregg2.Circuit.Emit.AttestedAutomatonRoute8Witness.strong_refuses_substitution' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms strong_refuses_substitution
/-- info: 'Dregg2.Circuit.Emit.AttestedAutomatonRoute8Witness.weak_accepts_substitution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms weak_accepts_substitution

/-- info: 'Dregg2.Circuit.Emit.AttestedAutomatonRoute8Witness.honest_strong_accepts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms honest_strong_accepts
/-- info: 'Dregg2.Circuit.Emit.AttestedAutomatonRoute8Witness.substitution_separation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms substitution_separation

#assert_all_clean [hash8_width, witness_canonical, witness_chip_sound, witness_ranges,
  row_root, row_opens, base_rows, route_rows, witness_satisfies, hash8_canonical, witness_pubroot,
  witness_commits, witness_payload, witness_record_canonical, witness_record_opens, witness_length,
  whole_theorem_inhabited, witness_no_residual, substitution_route_mismatch, honest_strong_accepts,
  strong_refuses_substitution, weak_accepts_substitution, substitution_separation]
end Dregg2.Circuit.Emit.AttestedAutomatonRoute8Witness

/-
# Ordered, length-bound exact-public DFA routing

The descriptor commits the complete transition table. Its eight public route
lanes commit the record's deterministic run, including domain and row position.
The public length is derived from the emitted AIR under canonical field readings
and trace height below the characteristic. The residual names a collision at
actual trace/record input blocks; there is no global hash-injectivity premise.
-/
import Dregg2.Circuit.Emit.DfaRoutingTableRoute8
import Dregg2.Circuit.Emit.RouteChain8Refine
import Dregg2.Circuit.Emit.RouteChain8Canonical
import Dregg2.Circuit.Emit.DfaRoutingTableBound

namespace Dregg2.Circuit.Emit.DfaRoutingTableRoute8Bound
open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.DfaRoutingTableEmit
open Dregg2.Circuit.Emit.DfaRoutingTableRoute8
open Dregg2.Circuit.Emit.DfaRoutingTableBound (readWord loopTbl loopDfa loopTbl_graph loopTbl_small)
open Dregg2.Circuit.Emit.RouteChain8
open Dregg2.Circuit.Emit.RouteChain8Refine
open Dregg2.Circuit.Emit.RouteChain8Canonical
open Dregg2.Circuit.Emit.RouteChain8Binding (fold preimage Collision find chain_binds_or_collides)
open Dregg2.Crypto.DfaAcceptanceAir (TableDfa classifyFrom)
set_option autoImplicit false

/-- Record preimages use the deterministic run of the same descriptor's DFA. -/
def runPayloads (d : TableDfa Nat Nat) : Nat → Nat → List Nat → List (List ℤ)
  | _, _, [] => []
  | q, i, y :: ys => [ROUTE_DOMAIN, (i+1 : Nat), q, y, d.step q y] ::
      runPayloads d (d.step q y) (i+1) ys

theorem runPayloads_length (d : TableDfa Nat Nat) : ∀ q i w,
    (runPayloads d q i w).length = w.length
  | _, _, [] => rfl
  | q, i, y :: ys => by simp [runPayloads, runPayloads_length d (d.step q y) (i+1) ys]

theorem runPayloads_width (d : TableDfa Nat Nat) : ∀ q i w,
    ∀ p ∈ runPayloads d q i w, p.length = 5
  | _, _, [], _, hp => by simp [runPayloads] at hp
  | q, i, y :: ys, p, hp => by
    simp only [runPayloads, List.mem_cons] at hp
    rcases hp with rfl | hp
    · rfl
    · exact runPayloads_width d (d.step q y) (i+1) ys p hp

theorem runPayloads_word (d : TableDfa Nat Nat) : ∀ q i w,
    (runPayloads d q i w).map (fun p => (p.getD 3 0).toNat) = w
  | _, _, [] => rfl
  | q, i, y :: ys => by
    change y :: (runPayloads d (d.step q y) (i+1) ys).map (fun p => (p.getD 3 0).toNat) = y :: ys
    rw [runPayloads_word d (d.step q y) (i+1) ys]

def recordFind (H : List ℤ → List ℤ) (t : VmTrace)
    (d : TableDfa Nat Nat) (q : Nat) (record : List Nat) : List ℤ × List ℤ :=
  find H (seed config t) (seed config t) (payloads config t) (runPayloads d q 0 record)

/-- The deployed residual is an actual full-output collision on two DISTINCT
canonical arity-16 chip inputs from this trace and this record. Field-representation
aliases and arbitrary unrelated collisions do not satisfy this evidence. -/
def RecordCollision (H : List ℤ → List ℤ) (t : VmTrace)
    (d : TableDfa Nat Nat) (q : Nat) (record : List Nat) : Prop :=
  let pair := recordFind H t d q record
  Collision H pair ∧ pair.1.length = 16 ∧ pair.2.length = 16 ∧
    CanonicalBlock pair.1 ∧ CanonicalBlock pair.2 ∧
    pair.1 ∈ RouteChain8Binding.preimages H (seed config t) (payloads config t) ∧
    pair.2 ∈ RouteChain8Binding.preimages H (seed config t) (runPayloads d q 0 record)

section Soundness
variable {hash : List ℤ → ℤ} {name : String} {tbl : List (List Nat)}
variable {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

theorem bound_rows
    (h : Satisfied2Public hash (tableRoutingBoundDesc name tbl) minit mfin maddrs t) :
    RowsHold config hash t := by
  intro i hi c hc
  exact h.rowConstraints i hi c (List.mem_append_right _ hc)

/-- Equality to the public length replaces the old caller-supplied equality to the
private trace's length. Full digest binding recovers the actual record, or names
a collision at this trace and this deterministic record run. -/
private theorem bound_word_or_collides_exactInt (H : List ℤ → List ℤ)
    (hs : ChipTableSoundN H (t.tf .poseidon2))
    (h : Satisfied2Public hash (tableRoutingBoundDesc name tbl) minit mfin maddrs t)
    (hc : Canonical t) (hne : t.rows ≠ []) (hheight : t.rows.length < 2013265921)
    (d : TableDfa Nat Nat) (q : Nat) (record : List Nat)
    (hlen : t.pub (lengthPi config) = (record.length : ℤ))
    (hopen : publicRoute config t = fold H (seed config t) (runPayloads d q 0 record)) :
    readWord t = record ∨ Collision H (recordFind H t d q record) := by
  have hr := bound_rows h
  have hl : t.rows.length = record.length := by
    have he := length_exact hr hc hne hheight
    exact Int.natCast_inj.mp (he.symm.trans hlen)
  have he : fold H (seed config t) (payloads config t) =
      fold H (seed config t) (runPayloads d q 0 record) :=
    (route_eq_fold H hs hr hc hne).symm.trans hopen
  rcases chain_binds_or_collides H 5 (seed config t) (payloads config t)
      (runPayloads d q 0 record) (payload_width config t) (runPayloads_width d q 0 record)
      (by simp [payloads, runPayloads_length, hl]) he with hp | hcollision
  · left
    have hm := congrArg (List.map (fun p : List ℤ => (p.getD 3 0).toNat)) hp
    rw [runPayloads_word] at hm
    simpa [payloads, payload, config, readWord, List.map_map, Function.comp_def] using hm
  · exact Or.inr hcollision

/-- The served binding claim: canonical fixed-width encoding is part of the
statement, so the named residual excludes modulo-field and framing aliases. -/
theorem bound_word_or_collides (H : List ℤ → List ℤ)
    (hwidth : ∀ input, (H input).length = 8)
    (hH : ∀ input, CanonicalBlock (H input))
    (hs : ChipTableSoundN H (t.tf .poseidon2))
    (h : Satisfied2Public hash (tableRoutingBoundDesc name tbl) minit mfin maddrs t)
    (hc : Canonical t) (hne : t.rows ≠ []) (hheight : t.rows.length < 2013265921)
    (d : TableDfa Nat Nat) (q : Nat) (record : List Nat)
    (hrecord : ∀ p ∈ runPayloads d q 0 record, CanonicalBlock p)
    (hlen : t.pub (lengthPi config) = (record.length : ℤ))
    (hopen : publicRoute config t = fold H (seed config t) (runPayloads d q 0 record)) :
    readWord t = record ∨ RecordCollision H t d q record := by
  rcases bound_word_or_collides_exactInt H hs h hc hne hheight d q record hlen hopen with hw | hcoll
  · exact Or.inl hw
  · right
    have hslen := seed_width config t
    have hsw := seed_canonical config t hc
    have hp := trace_payloads_canonical config t hc (by decide : config.domain < 2013265921)
    have hl := RouteChain8Binding.find_arity H hwidth (payloads config t)
      (runPayloads d q 0 record) (seed config t) (seed config t) hslen hslen
      (payload_width config t) (runPayloads_width d q 0 record) hcoll
    have hcan := collision_inputs_canonical H hH (payloads config t) (runPayloads d q 0 record)
      (seed config t) (seed config t) hsw hsw hp hrecord hcoll
    have hm := RouteChain8Binding.find_mem H (payloads config t) (runPayloads d q 0 record)
      (seed config t) (seed config t) hcoll.1
    exact ⟨hcoll, hl.1, hl.2, hcan.1, hcan.2, hm⟩

/-- Classification is inherited from the certified table lowering, now of the
PUBLICLY OPENED RECORD rather than merely a word read from a private trace. -/
theorem bound_classifies_or_collides (H : List ℤ → List ℤ)
    (hwidth : ∀ input, (H input).length = 8)
    (hH : ∀ input, CanonicalBlock (H input))
    (hs : ChipTableSoundN H (t.tf .poseidon2))
    (h : Satisfied2Public hash (tableRoutingBoundDesc name tbl) minit mfin maddrs t)
    (hc : Canonical t) (hne : t.rows ≠ []) (hheight : t.rows.length < 2013265921)
    (d : TableDfa Nat Nat)
    (htbl : ∀ r ∈ tbl, ∃ s y, r = [s,y,d.step s y])
    (hsmall : ∀ r ∈ tbl, ∀ v ∈ r, v < 2013265921)
    (q fin : Nat) (hq : q < 2013265921) (hf : fin < 2013265921)
    (hstart : t.pub PI_INITIAL = q) (hfinal : t.pub PI_FINAL = fin)
    (record : List Nat) (hrecord : ∀ p ∈ runPayloads d q 0 record, CanonicalBlock p)
    (hlen : t.pub (lengthPi config) = (record.length : ℤ))
    (hopen : publicRoute config t = fold H (seed config t) (runPayloads d q 0 record)) :
    (readWord t = record ∧ fin = classifyFrom d q record) ∨
      RecordCollision H t d q record := by
  rcases bound_word_or_collides H hwidth hH hs h hc hne hheight d q record hrecord hlen hopen with hw | hcollision
  · left
    refine ⟨hw, ?_⟩
    have hf' := (tableRouting_refines_classify d htbl hsmall (forget_bound h)
      hne q hstart hq fin hfinal hf).2
    simpa only [← hw, readWord] using hf'
  · exact Or.inr hcollision
end Soundness

/-! A complete satisfying two-row witness, not merely an algebraic fold example. -/
def witnessHash (input : List ℤ) : List ℤ :=
  (RouteChain8Binding.exampleHash input).map (fun x => x % 2013265921)

theorem witnessHash_width (input : List ℤ) : (witnessHash input).length = 8 := rfl

theorem witnessHash_canonical (input : List ℤ) :
    ∀ x ∈ witnessHash input, 0 ≤ x ∧ x < 2013265921 := by
  intro x hx
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
  exact ⟨Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide)⟩
def witnessRow1 : Assignment := fun c =>
  ([0,1,0, 0,0,0,0,0,0,0,0, 1,1,2,3,4,5,6,7, 1] : List ℤ).getD c 0
def witnessRow2 : Assignment := fun c =>
  ([0,2,0, 1,1,2,3,4,5,6,7, 5,1,2,3,4,5,6,7, 2] : List ℤ).getD c 0
def witnessPub : Assignment := fun c => ([0,0,5,1,2,3,4,5,6,7,2] : List ℤ).getD c 0
def witnessChip : Table :=
  [chipRowN witnessHash ((inputs config).map (·.eval witnessRow1)),
   chipRowN witnessHash ((inputs config).map (·.eval witnessRow2))]
def witnessTf : TraceFamily := fun id =>
  if id = TRT_TID then exactPublicTable loopTbl else
  if id = .poseidon2 then witnessChip else []
def witness : VmTrace :=
  { rows := [witnessRow1,witnessRow2], pub := witnessPub, tf := witnessTf }

theorem witness_chip_sound : ChipTableSoundN witnessHash (witness.tf .poseidon2) := by
  intro r hr
  change r ∈ witnessChip at hr
  simp only [witnessChip, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, by decide, rfl⟩
  · exact ⟨_, by decide, rfl⟩

theorem memLog_bound (t : VmTrace) : memLog demoBoundDesc t = [] := by
  simp only [demoBoundDesc, tableRoutingBoundDesc, memLog, memOps_decorate]
  simp [memOpsOf, tableRoutingDesc_constraints]
theorem mapLog_bound (t : VmTrace) : mapLog demoBoundDesc t = [] := by
  simp only [demoBoundDesc, tableRoutingBoundDesc, mapLog, mapOps_decorate]
  simp [mapOpsOf, tableRoutingDesc_constraints]

theorem witness_satisfies :
    Satisfied2Public hash0 demoBoundDesc (fun _ => 0) (fun _ => (0,0)) [] witness where
  rowConstraints := by
    intro i hi c hc
    have hi2 : i < 2 := hi
    simp only [demoBoundDesc, tableRoutingBoundDesc, decorate, tableRoutingDesc_constraints,
      constraints, lanes, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    interval_cases i <;> rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      norm_num [VmConstraint2.holdsAt, VmConstraint.holdsVm, Lookup.holdsAt,
        WindowConstraint.holdsAt, envAt, witness, witnessRow1, witnessRow2, witnessPub,
        witnessTf, witnessChip, witnessHash, RouteChain8Binding.exampleHash,
        chipRowN, padTo, chipLookupTupleN, padToE, inputs, chip, copy, seedPin, outputPin,
        indexFirst, indexStep, indexLast, config, lanes, acc, out, index, routePi, lengthPi,
        exactPublicTable, loopTbl, contWindowBody_eq, WindowExpr.eval, EmittedExpr.eval,
        CURRENT, SYMBOL, NEXT, PI_INITIAL, PI_FINAL, TRT_TID, TRT_WIDTH, TRT_PI_COUNT] <;> decide
  rowHashes := by intro i _; trivial
  rowRanges := by intro i _ r hr; simp [demoBoundDesc, tableRoutingBoundDesc, decorate,
    tableRoutingDesc_ranges] at hr
  memAddrsNodup := List.nodup_nil
  memClosed := by rw [memLog_bound]; simp
  memDisciplined := by rw [memLog_bound]; trivial
  memBalanced := by rw [memLog_bound]; exact memCheck_nil _ _
  memTableFaithful := by rw [memLog_bound]; rfl
  mapTableFaithful := by rw [mapLog_bound]; rfl
  publicTablesFaithful := by
    intro td htd
    simp only [demoBoundDesc, tableRoutingBoundDesc, decorate, tableRoutingDesc_tables,
      List.mem_append, List.mem_singleton] at htd
    rcases htd with rfl | rfl
    · rfl
    · trivial
  publicLookupBalanced := by
    intro td htd
    simp only [demoBoundDesc, tableRoutingBoundDesc, decorate, tableRoutingDesc_tables,
      List.mem_append, List.mem_singleton] at htd
    rcases htd with rfl | rfl
    · show (lookupLog demoBoundDesc witness TRT_TID).Perm (exactPublicTable loopTbl)
      rw [demoBoundDesc, tableRoutingBoundDesc, lookupLog_decorate _ _ _ _ _ (by decide),
        DfaRoutingTableBound.lookupLog_eq]
      exact List.Perm.refl _
    · trivial

private theorem list_canonical : ∀ (xs : List ℤ),
    (∀ x ∈ xs, 0 ≤ x ∧ x < 2013265921) → ∀ j, 0 ≤ xs.getD j 0 ∧ xs.getD j 0 < 2013265921
  | [], _, _ => by simp
  | a :: _, h, 0 => h a List.mem_cons_self
  | _ :: xs, h, j+1 => list_canonical xs (fun x hx => h x (List.mem_cons_of_mem _ hx)) j

theorem witness_canonical : Canonical witness where
  row := by
    intro i hi j
    have hi2 : i < 2 := hi
    interval_cases i
    · exact list_canonical _ (by decide) j
    · exact list_canonical _ (by decide) j
  pub := fun j => list_canonical _ (by decide) j

/-- The honest record's public opening and public length. -/
theorem witness_opens :
    publicRoute config witness = fold witnessHash (seed config witness)
      (runPayloads loopDfa 0 0 [1,2]) ∧
    witness.pub (lengthPi config) = ([1,2].length : ℤ) := by
  constructor <;> decide

/-- The opened honest record follows the same payload sequence, excluding the
collision branch without assuming anything about the compression function. -/
theorem witness_no_collision :
    ¬ Collision witnessHash (recordFind witnessHash witness loopDfa 0 [1,2]) := by
  have hp : payloads config witness = runPayloads loopDfa 0 0 [1,2] := rfl
  simp only [recordFind, ← hp]
  exact RouteChain8Binding.no_self_collision _ _ _

/-- The whole record-classification theorem fires on the complete AIR witness. -/
theorem witness_bound_classifies : readWord witness = [1,2] ∧
    (0 : Nat) = classifyFrom loopDfa 0 [1,2] := by
  have h := bound_classifies_or_collides witnessHash witnessHash_width witnessHash_canonical
    witness_chip_sound witness_satisfies witness_canonical (by decide) (by decide)
    loopDfa loopTbl_graph loopTbl_small 0 0 (by decide) (by decide) rfl rfl [1,2]
    (by unfold CanonicalBlock; decide) witness_opens.2 witness_opens.1
  exact h.resolve_right (fun hc => witness_no_collision hc.1)

/-- Legacy acceptance ignores the supplied record; the new acceptance consumes
its actual ordered opening and public length. -/
def WeakAccepts (_record : List Nat) : Prop :=
  Satisfied2Public hash0 (tableRoutingDesc "dregg-dfa-routing-table::route8-bound-v1" loopTbl)
    (fun _ => 0) (fun _ => (0,0)) [] witness

def StrongAccepts (record : List Nat) : Prop :=
  Satisfied2Public hash0 demoBoundDesc (fun _ => 0) (fun _ => (0,0)) [] witness ∧
    publicRoute config witness = fold witnessHash (seed config witness)
      (runPayloads loopDfa 0 0 record) ∧
    witness.pub (lengthPi config) = (record.length : ℤ)

theorem honest_strong_accepts : StrongAccepts [1,2] :=
  ⟨witness_satisfies, witness_opens⟩

theorem order_splice_weak_accepts : WeakAccepts [2,1] := forget_bound witness_satisfies

theorem order_splice_strong_refuses : ¬ StrongAccepts [2,1] := by
  intro h
  have hne : publicRoute config witness ≠ fold witnessHash (seed config witness)
      (runPayloads loopDfa 0 0 [2,1]) := by decide
  exact hne h.2.1

/-- Public length refuses a shortened record independently of the route value. -/
theorem length_splice_strong_refuses : ¬ StrongAccepts [1] := by
  intro h
  have hne : witness.pub (lengthPi config) ≠ ([1].length : ℤ) := by decide
  exact hne h.2.2

/-- info: 'Dregg2.Circuit.Emit.DfaRoutingTableRoute8Bound.bound_word_or_collides' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms bound_word_or_collides
/-- info: 'Dregg2.Circuit.Emit.DfaRoutingTableRoute8Bound.bound_classifies_or_collides' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms bound_classifies_or_collides
/-- info: 'Dregg2.Circuit.Emit.DfaRoutingTableRoute8Bound.witness_satisfies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms witness_satisfies
/-- info: 'Dregg2.Circuit.Emit.DfaRoutingTableRoute8Bound.witness_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms witness_canonical
/-- info: 'Dregg2.Circuit.Emit.DfaRoutingTableRoute8Bound.witness_bound_classifies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms witness_bound_classifies
/-- info: 'Dregg2.Circuit.Emit.DfaRoutingTableRoute8Bound.honest_strong_accepts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms honest_strong_accepts
/-- info: 'Dregg2.Circuit.Emit.DfaRoutingTableRoute8Bound.order_splice_weak_accepts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms order_splice_weak_accepts
/-- info: 'Dregg2.Circuit.Emit.DfaRoutingTableRoute8Bound.order_splice_strong_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms order_splice_strong_refuses
/-- info: 'Dregg2.Circuit.Emit.DfaRoutingTableRoute8Bound.length_splice_strong_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms length_splice_strong_refuses
end Dregg2.Circuit.Emit.DfaRoutingTableRoute8Bound

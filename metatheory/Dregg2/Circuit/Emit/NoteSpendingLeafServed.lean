import Dregg2.Circuit.Emit.NoteSpendingLeafRung2
/-! The served note-spend artifact is the existing last-row repair. These bridges
preserve the explicit path-shape, chip-table and canonicality hypotheses; they do
not identify the scalar fact-hash tree with the deployed Faithful8 note tree. -/
namespace Dregg2.Circuit.Emit.NoteSpendingLeafServed
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.NoteSpendingLeafEmit
open Dregg2.Circuit.Emit.NoteSpendingLeafRefine
open Dregg2.Circuit.Emit.NoteSpendingLeafRung2
set_option autoImplicit false

theorem fixed_implies_base {hash : List Int → Int} {minit : Int → Int}
    {mfin : Int → Int × Nat} {maddrs : List Int} {t : VmTrace}
    (h : Satisfied2 hash noteSpendLeafDescFixed minit mfin maddrs t) :
    Satisfied2 hash noteSpendLeafDesc minit mfin maddrs t := by
  have hm : memLog noteSpendLeafDescFixed t = memLog noteSpendLeafDesc t := rfl
  have ha : mapLog noteSpendLeafDescFixed t = mapLog noteSpendLeafDesc t := rfl
  refine ⟨?_, h.rowHashes, h.rowRanges, h.memAddrsNodup, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi c hc
    exact h.rowConstraints i hi c (List.mem_append_left _ hc)
  · simpa only [hm] using h.memClosed
  · simpa only [hm] using h.memDisciplined
  · simpa only [hm] using h.memBalanced
  · simpa only [hm] using h.memTableFaithful
  · simpa only [ha] using h.mapTableFaithful

theorem served_spend_spec {permOut : List Int → List Int} {hash : List Int → Int}
    {minit : Int → Int} {mfin : Int → Int × Nat} {maddrs : List Int} {t : VmTrace}
    (h : Satisfied2 hash noteSpendLeafDescFixed minit mfin maddrs t)
    (hchip : ChipTableSoundN permOut (t.tf .poseidon2))
    (hlen : 1 < t.rows.length) (hspend : (envAt t 0).loc IS_MERKLE = 0)
    (hcanon : NoteCanon (envAt t 0)) : NoteSpendLeafSpec permOut (envAt t 0) :=
  noteSpend_satisfied2_spec permOut hash minit mfin maddrs t
    (fixed_implies_base h) hchip hlen hspend hcanon

theorem served_committed_note_member {permOut : List Int → List Int} {hash : List Int → Int}
    {minit : Int → Int} {mfin : Int → Int × Nat} {maddrs : List Int} {t : VmTrace}
    (h : Satisfied2 hash noteSpendLeafDescFixed minit mfin maddrs t)
    (hchip : ChipTableSoundN permOut (t.tf .poseidon2))
    (hlen : 2 ≤ t.rows.length) (hspend : (envAt t 0).loc IS_MERKLE = 0)
    (hcanon : NoteCanon (envAt t 0)) (hmcanon : MerkleThreadCanon t)
    (hpath : ∀ i, 1 ≤ i → i + 1 < t.rows.length → (envAt t i).loc IS_MERKLE = 1) :
    (envAt t 0).loc 5 = (permOut (firingIns (envAt t 0) [53, 45, 46, 47])).headD 0 ∧
    MembersAtRoot permOut ((envAt t 0).loc 5) (t.pub 1) (merklePathSteps t) :=
  noteSpend_committed_note_member (fixed_implies_base h) hchip hlen hspend hcanon hmcanon hpath

theorem served_honest : Satisfied2 (fun _ => 0) noteSpendLeafDescFixed
    (fun _ => 0) (fun _ => (0, 0)) [] witnessTrace := fixed_accepts_honest_witness

theorem served_refuses_old_forge : ¬ Satisfied2 (fun _ => 0) noteSpendLeafDescFixed
    (fun _ => 0) (fun _ => (0, 0)) [] forgeTrace := forge_rejected_by_fix _ _ _ _

/-- All hypotheses of the composed member theorem hold together on one trace.
The witness permutation is the existing abstract constant permutation, not a claim
about cryptographic collision resistance or a deployed Faithful8 tree. -/
theorem served_member_inhabited :
    Satisfied2 (fun _ => 0) noteSpendLeafDescFixed (fun _ => 0) (fun _ => (0, 0)) [] witnessTrace ∧
    ChipTableSoundN witnessPerm (witnessTrace.tf .poseidon2) ∧
    2 ≤ witnessTrace.rows.length ∧ (envAt witnessTrace 0).loc IS_MERKLE = 0 ∧
    NoteCanon (envAt witnessTrace 0) ∧ MerkleThreadCanon witnessTrace ∧
    (∀ i, 1 ≤ i → i + 1 < witnessTrace.rows.length → (envAt witnessTrace i).loc IS_MERKLE = 1) := by
  refine ⟨served_honest, witness_chipSound, by decide, by decide, witness_canon, ?_, ?_⟩
  · exact ⟨by intro i hi
              have hl : witnessTrace.rows.length = 2 := rfl
              rw [hl] at hi
              have : i = 0 := by omega
              subst this
              exact ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩,
            ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩
  · intro i h1 h2; have hl : witnessTrace.rows.length = 2 := rfl; omega

theorem served_member_witness :
    (envAt witnessTrace 0).loc 5 =
      (witnessPerm (firingIns (envAt witnessTrace 0) [53, 45, 46, 47])).headD 0 ∧
    MembersAtRoot witnessPerm ((envAt witnessTrace 0).loc 5) (witnessTrace.pub 1)
      (merklePathSteps witnessTrace) := by
  obtain ⟨hs, hc, hl, hr, hn, hm, hp⟩ := served_member_inhabited
  exact served_committed_note_member hs hc hl hr hn hm hp

/-- The identical trace passes the old AST and fails the consumed AST. The old
acceptance uses its abstract table; it is not a real Poseidon2 proof forgery. -/
theorem repair_separates_same_trace :
    Satisfied2 (fun _ => 0) noteSpendLeafDesc (fun _ => 0) (fun _ => (0, 0)) [] forgeTrace ∧
    ¬ Satisfied2 (fun _ => 0) noteSpendLeafDescFixed (fun _ => 0) (fun _ => (0, 0)) [] forgeTrace :=
  ⟨forgeTrace_satisfied2, served_refuses_old_forge⟩

/-- info: 'Dregg2.Circuit.Emit.NoteSpendingLeafServed.fixed_implies_base' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms fixed_implies_base
/-- info: 'Dregg2.Circuit.Emit.NoteSpendingLeafServed.served_spend_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms served_spend_spec
/-- info: 'Dregg2.Circuit.Emit.NoteSpendingLeafServed.served_committed_note_member' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms served_committed_note_member
/-- info: 'Dregg2.Circuit.Emit.NoteSpendingLeafServed.served_honest' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms served_honest
/-- info: 'Dregg2.Circuit.Emit.NoteSpendingLeafServed.served_refuses_old_forge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms served_refuses_old_forge
/-- info: 'Dregg2.Circuit.Emit.NoteSpendingLeafServed.served_member_inhabited' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms served_member_inhabited
/-- info: 'Dregg2.Circuit.Emit.NoteSpendingLeafServed.served_member_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms served_member_witness
/-- info: 'Dregg2.Circuit.Emit.NoteSpendingLeafServed.repair_separates_same_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms repair_separates_same_trace
#assert_all_clean [fixed_implies_base, served_spend_spec, served_committed_note_member,
  served_honest, served_refuses_old_forge, served_member_inhabited, served_member_witness, repair_separates_same_trace]
end Dregg2.Circuit.Emit.NoteSpendingLeafServed

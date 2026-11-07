/-
# Statement audit evidence, initiative register row 1 (parser/language excellence).

These facts inhabit actual checker premises and separate weakened checkers from the production
checker. They do not prove cryptographic strength of the reference hash, completeness of an
implementation extraction, or the correctness of an arbitrary policy table. The paired review
manifest records those boundaries and binds the reviewed source. Exact axiom reports below are
checked by Lean; the Python gate checks source identity and evidence coverage only.
-/
import Dregg2.Datalog.SafeCoincidence
import Dregg2.Automata.TableRunSpec
import Dregg2.Automata.DfaBoundReference

set_option maxRecDepth 4096

namespace Dregg2.Automata.StatementAudit

open Dregg2.Datalog
open FixpointCert.Reference (hash0)

/-- Domain order and multiplicity do not affect the optimized checker. This lets the kernel
check concrete witnesses without evaluating the well-founded sorting implementation. -/
theorem runStrataJ_domain_congr {P : StratifiedCert.SProgram} {d₁ d₂ : List Int}
    (hd : ∀ x, x ∈ d₁ ↔ x ∈ d₂) :
    ∀ (strata : StratifiedCert.Strata) (ts : List FixpointCert.Trace) (db : List FixpointCert.Fact),
      JoinClosure.runStrataJ P d₁ strata ts db = JoinClosure.runStrataJ P d₂ strata ts db
  | [], [], _ => rfl
  | [], _ :: _, _ => rfl
  | _ :: _, [], _ => rfl
  | S :: rest, t :: ts, db => by
    simp only [JoinClosure.runStrataJ, JoinClosure.replayS_congr hd]
    cases StratifiedCert.replayS P d₂ S db db t.rounds with
    | none => rfl
    | some db' =>
      simp only
      split
      · exact runStrataJ_domain_congr hd rest ts db'
      · rfl

/-- Both the optimized checker and its safety requirement have a nontrivial accepted instance. -/
theorem join_accepts :
    JoinClosure.verifyJ hash0 (StratifiedCert.Reference.revStmt 1)
      ⟨StratifiedCert.Reference.revEdb, StratifiedCert.Reference.revHonest⟩ = true := by
  unfold JoinClosure.verifyJ
  rw [runStrataJ_domain_congr (JoinClosure.mem_domFast _ _)]
  decide

/-- A budget instance with a positive total and a refunded charge: all premises of the
sum-soundness theorem are inhabited, including the accumulator check. -/
theorem budget_accepts :
    Aggregates.verifyBudget hash0 (Aggregates.Reference.billStmt 10)
      Aggregates.Reference.honestB = true := by decide

/-- The optimized budget checker accepts the same nontrivial certificate. -/
theorem join_budget_accepts :
    JoinClosure.verifyBudgetJ hash0 (Aggregates.Reference.billStmt 10)
      Aggregates.Reference.honestB = true := by
  unfold JoinClosure.verifyBudgetJ JoinClosure.verifyJ
  simp only [runStrataJ_domain_congr (JoinClosure.mem_domFast _ _)]
  decide

/-- The weak budget check accepts the false low total; the actual checker refuses it. -/
theorem budget_separation :
    Aggregates.Reference.verifyTrustFinal hash0 (Aggregates.Reference.billStmt 8)
      Aggregates.Reference.tamperedB = true ∧
    Aggregates.verifyBudget hash0 (Aggregates.Reference.billStmt 8)
      Aggregates.Reference.tamperedB = false :=
  ⟨Aggregates.Reference.tampered_accepted_by_trustFinal,
    Aggregates.Reference.tampered_refused_by_verifyBudget⟩

/-- A zero rejection receipt on an actual record, including the nullable/empty-word boundary. -/
theorem table_accepts : TableRun.rejectCount TableRun.noA [⟨#[]⟩] = 0 := by decide

/-- A deliberately undersized table exposes the total runner's fallback behavior. It is an audit
counterexample, not a compiler output. -/
def fallbackTable : TableRun.FlatTable := ⟨2, #[], 1, [1]⟩

/-- Semantic agreement with a total table does not certify its well-formedness. The separate
wellFormed check refuses the same table whose empty word the runner accepts. -/
theorem table_validation_separation :
    TableRun.acceptsBytes fallbackTable ⟨#[]⟩ = true ∧
    (fallbackTable.wellFormed && TableRun.acceptsBytes fallbackTable ⟨#[]⟩) = false := by decide

/-- The count theorem covers only its supplied list. Omitting a rejected record changes its
count; external corpus coverage is a separate obligation. -/
theorem table_omission_changes_count :
    TableRun.rejectCount fallbackTable [⟨#[]⟩] = 0 ∧
    TableRun.rejectCount fallbackTable [⟨#[]⟩, ⟨#[0]⟩] = 1 := by decide

end Dregg2.Automata.StatementAudit

/-- info: 'Dregg2.Datalog.FixpointCert.verify_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Dregg2.Datalog.FixpointCert.verify_sound
/-- info: 'Dregg2.Datalog.FixpointCert.Reference.honest_verifies' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Dregg2.Datalog.FixpointCert.Reference.honest_verifies
/-- info: 'Dregg2.Datalog.FixpointCert.Reference.open_trace_separation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Dregg2.Datalog.FixpointCert.Reference.open_trace_separation
/-- info: 'Dregg2.Datalog.StratifiedCert.verifyS_receipt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Dregg2.Datalog.StratifiedCert.verifyS_receipt
/-- info: 'Dregg2.Datalog.StratifiedCert.Reference.honest_count0_verifies' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Dregg2.Datalog.StratifiedCert.Reference.honest_count0_verifies
/-- info: 'Dregg2.Datalog.StratifiedCert.Reference.current_db_separation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Dregg2.Datalog.StratifiedCert.Reference.current_db_separation
/-- info: 'Dregg2.Datalog.JoinClosure.verifyJ_verifyS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Dregg2.Datalog.JoinClosure.verifyJ_verifyS
/-- info: 'Dregg2.Datalog.JoinClosure.Reference.join_safety_separation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Dregg2.Datalog.JoinClosure.Reference.join_safety_separation
/-- info: 'Dregg2.Datalog.SafeCoincidence.verifyJ_receipt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Dregg2.Datalog.SafeCoincidence.verifyJ_receipt
/-- info: 'Dregg2.Datalog.SafeCoincidence.Reference.unsafe_semantics_differ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Dregg2.Datalog.SafeCoincidence.Reference.unsafe_semantics_differ
/-- info: 'Dregg2.Datalog.Aggregates.verifyBudget_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Dregg2.Datalog.Aggregates.verifyBudget_sound
/-- info: 'Dregg2.Crypto.Dfa.dfa_bound_identifies_record_or_collides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Dregg2.Crypto.Dfa.dfa_bound_identifies_record_or_collides
/-- info: 'Dregg2.Crypto.Dfa.Reference.aab_accepts' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Dregg2.Crypto.Dfa.Reference.aab_accepts
/-- info: 'Dregg2.Crypto.Dfa.Reference.splice_fails_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Dregg2.Crypto.Dfa.Reference.splice_fails_bound
/-- info: 'Dregg2.Automata.TableRun.rejectCount_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Dregg2.Automata.TableRun.rejectCount_eq_zero_iff
/-- info: 'Dregg2.Automata.StatementAudit.join_accepts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Dregg2.Automata.StatementAudit.join_accepts
/-- info: 'Dregg2.Automata.StatementAudit.runStrataJ_domain_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Dregg2.Automata.StatementAudit.runStrataJ_domain_congr
/-- info: 'Dregg2.Automata.StatementAudit.budget_accepts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Dregg2.Automata.StatementAudit.budget_accepts
/-- info: 'Dregg2.Automata.StatementAudit.join_budget_accepts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Dregg2.Automata.StatementAudit.join_budget_accepts
/-- info: 'Dregg2.Automata.StatementAudit.budget_separation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Dregg2.Automata.StatementAudit.budget_separation
/-- info: 'Dregg2.Automata.StatementAudit.table_accepts' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Dregg2.Automata.StatementAudit.table_accepts
/-- info: 'Dregg2.Automata.StatementAudit.table_omission_changes_count' does not depend on any axioms -/
#guard_msgs in
#print axioms Dregg2.Automata.StatementAudit.table_omission_changes_count

/-- info: 'Dregg2.Automata.StatementAudit.table_validation_separation' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Dregg2.Automata.StatementAudit.table_validation_separation

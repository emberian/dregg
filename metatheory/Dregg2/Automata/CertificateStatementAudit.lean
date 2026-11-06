/- Kernel evidence tying the committed certificate families to positive and negative instances. -/
import Dregg2.Sat.LratCert
import Dregg2.Crypto.Deriv.BisimCert
import Dregg2.Policy.Compositional

namespace Dregg2.Automata.CertificateStatementAudit

open Dregg2.Sat.LratCert

/-- Removing RUP admits a false UNSAT claim at the correct root. The production verifier rejects
the same statement/certificate, and a concrete satisfying assignment disproves its claim. -/
theorem lrat_false_claim_separation :
    Reference.verifyNoRup Reference.hash0 Reference.satStmt
      ⟨Reference.satCnf, Reference.forgedEmpty⟩ = true ∧
    verify Reference.hash0 Reference.satStmt ⟨Reference.satCnf, Reference.forgedEmpty⟩ = false ∧
    Satisfies (fun _ => true) Reference.satCnf :=
  ⟨Reference.forged_accepted_by_noRup, Reference.forged_refused, Reference.satCnf_sat⟩

/-- info: 'Dregg2.Automata.CertificateStatementAudit.lrat_false_claim_separation' depends on axioms: [propext] -/
#guard_msgs in
#print axioms lrat_false_claim_separation
/-- info: 'Dregg2.Sat.LratCert.Reference.php3_verified' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Dregg2.Sat.LratCert.Reference.php3_verified
/-- info: 'Dregg2.Crypto.Deriv.BisimCert.Reference.upgrade_holds_or_collides' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Dregg2.Crypto.Deriv.BisimCert.Reference.upgrade_holds_or_collides

/-- info: 'Dregg2.Policy.Compiled.memo_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Dregg2.Policy.Compiled.memo_eq
/-- info: 'Dregg2.Policy.cachedIdx_distinguishes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Dregg2.Policy.cachedIdx_distinguishes
/-- info: 'Dregg2.Policy.cached_zero_fuel' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Dregg2.Policy.cached_zero_fuel
/-- info: 'Dregg2.Policy.Certified.hdec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Dregg2.Policy.Certified.hdec

end Dregg2.Automata.CertificateStatementAudit

/-
# Live direct-logic certificates for DREGG decision predicates

The optimizer's small `factorSpecimen` is useful as a unit test, but it is not
an application workload.  This module lowers four named decisions that are
actually consumed by the DREGG development:

* `Exec.Admission.admissible` (`Exec/Admission.lean`): the fail-closed turn
  prologue, including receipt-head binding;
* `Upgrade.AuthorizedUpgrade` (`Upgrade.lean`): control-cap, subject, and
  current-proof/owner-signature authorization;
* `CredentialAttenuation.Clearance.admits`
  (`Authority/CredentialAttenuation.lean`): the deployed structured credential
  clearance decision; and
* `StrandAdmission.admitted` (`Distributed/StrandAdmission.lean`): the
  stake/vouch gate placed in front of finality.

For predicates with a genuine sum-of-products branch, `source` is the naive
branch-expanded Boolean skeleton and the certified target shares the common
conjunct.  Every atom is the exact source predicate named below.  Arithmetic,
list membership, lifecycle, capability lookup, and receipt comparison remain
atomic here: the theorem is about the Boolean decision skeleton, not a claim
that these operations have themselves been arithmetized by this module.

Standalone and additive: no umbrella import is changed here.
-/

import Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2
import Dregg2.Exec.Admission
import Dregg2.Upgrade
import Dregg2.Authority.CredentialAttenuation
import Dregg2.Distributed.StrandAdmission

namespace Dregg2.Metatheory.DirectLogicDreggWorkloads

open Dregg2.Metatheory.DirectLogicOptimizerCertificate
open Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2
open Dregg2.Circuit.DescriptorIR2 (Satisfied2 VmTrace)

set_option autoImplicit false

abbrev Formula := Dregg2.Metatheory.DirectLogicOptimizerCertificate.Formula

private def a0 {n : Nat} (h : 0 < n := by omega) : Formula n := .atom ⟨0, h⟩
private def a1 {n : Nat} (h : 1 < n := by omega) : Formula n := .atom ⟨1, h⟩
private def a2 {n : Nat} (h : 2 < n := by omega) : Formula n := .atom ⟨2, h⟩
private def a3 {n : Nat} (h : 3 < n := by omega) : Formula n := .atom ⟨3, h⟩
private def a4 {n : Nat} (h : 4 < n := by omega) : Formula n := .atom ⟨4, h⟩
private def a5 {n : Nat} (h : 5 < n := by omega) : Formula n := .atom ⟨5, h⟩
private def a6 {n : Nat} (h : 6 < n := by omega) : Formula n := .atom ⟨6, h⟩
private def a7 {n : Nat} (h : 7 < n := by omega) : Formula n := .atom ⟨7, h⟩
private def a8 {n : Nat} (h : 8 < n := by omega) : Formula n := .atom ⟨8, h⟩
private def a9 {n : Nat} (h : 9 < n := by omega) : Formula n := .atom ⟨9, h⟩
private def a10 {n : Nat} (h : 10 < n := by omega) : Formula n := .atom ⟨10, h⟩
private def a11 {n : Nat} (h : 11 < n := by omega) : Formula n := .atom ⟨11, h⟩

/-! ## 1. Turn admission, including receipt-head self-binding

Provenance: `Dregg2.Exec.Admission.admissible`.  Its expiry match is the real
two-arm branch.  The branch-expanded skeleton duplicates every other admission
gate and therefore gives the optimizer a non-toy common-factor opportunity.
-/

namespace AdmissionWorkload

open Dregg2.Exec
open Dregg2.Exec.Admission

/-- The ten gates common to both `validUntil` arms. -/
def common : Formula 12 :=
  .and (a0)
    (.and (a1)
      (.and (a2)
        (.and (a5)
          (.and (a6)
            (.and (a7)
              (.and (a8)
                (.and (a9) (.and (a10) (a11)))))))))

/-- Naive branch expansion of
`common && (validUntil = none || validUntil = some vu && expiryOk clock (some vu))`. -/
def source : Formula 12 :=
  .or (.and common (a3)) (.and common (a4))

/-- Exact atoms of `Exec.Admission.admissible`.  Atom 3/4 are the two expiry
branches; the remaining atoms are the gates shared by those branches. -/
def truth (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState) : Fin 12 → Prop
  | ⟨0, _⟩ => h.forestNonEmpty = true
  | ⟨1, _⟩ => h.agent ∈ s.kernel.accounts
  | ⟨2, _⟩ => cellLifecycleCanAuthor s.kernel h.agent = true
  | ⟨3, _⟩ => h.validUntil = none
  | ⟨4, _⟩ => ∃ vu, h.validUntil = some vu ∧ expiryOk (admissionClock ctx) (some vu) = true
  | ⟨5, _⟩ => h.nonce = storedNonce s h.agent
  | ⟨6, _⟩ => 0 ≤ h.fee
  | ⟨7, _⟩ => h.fee ≤ storedBalance s h.agent
  | ⟨8, _⟩ => (!isFrozen ctx h.agent) = true
  | ⟨9, _⟩ => h.writeSet.all (fun c => !isFrozen ctx c) = true
  | ⟨10, _⟩ => h.prevReceipt = ctx.storedHead
  | ⟨11, _⟩ => h.fee ≤ (ctx.budget : Int)
  | ⟨_, _⟩ => False

/-- All-input equivalence to the production turn-admission decision.  This is
the Boolean skeleton only; the arithmetic and container operations named by
the atoms retain their existing implementations. -/
theorem source_iff_admissible (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState) :
    Formula.Holds (truth ctx h s) source ↔ admissible ctx h s = true := by
  cases hv : h.validUntil with
  | none =>
      simp only [source, common, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, Formula.Holds]
      simp only [truth]
      simp [admissible, hv]
      aesop
  | some vu =>
      simp only [source, common, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, Formula.Holds]
      simp only [truth]
      simp [admissible, hv]
      aesop

def certificate : PublicLiveCertificate 12 := certifyPublic source

theorem optimized_iff_admissible (ctx : AdmCtx) (h : TurnHdr) (s : RecChainedState) :
    Formula.Holds (truth ctx h s) certificate.optimized ↔ admissible ctx h s = true := by
  rw [← source_iff_admissible]
  exact (optimize_holds_iff (truth ctx h s) source).symm

end AdmissionWorkload

/-! ## 2. Authorized anti-brick program upgrade

Provenance: `Dregg2.Upgrade.AuthorizedUpgrade`.  The actual authorization is a
control-cap and subject prefix followed by a sum type: current-version proof or
owner signature.  Expanding those two constructors duplicates the authority
prefix; the certificate shares it again.
-/

namespace UpgradeWorkload

open Dregg2.Upgrade

def authorityPrefix : Formula 4 := .and (a0) (a1)

def source : Formula 4 :=
  .or (.and authorityPrefix (a2)) (.and authorityPrefix (a3))

def truth (caps : Dregg2.Authority.Caps) (t : UpgradeTurn) : Fin 4 → Prop
  | ⟨0, _⟩ => ownerHoldsControl caps t.owner
  | ⟨1, _⟩ => t.owner ∈ t.subjects
  | ⟨2, _⟩ => ∃ v, t.auth = .byProof v ∧ v = t.live
  | ⟨3, _⟩ => t.auth = .bySignature
  | ⟨_, _⟩ => False

/-- Exact all-input equivalence to `Upgrade.AuthorizedUpgrade`; the capability
membership atom is not replaced by a toy Boolean. -/
theorem source_iff_authorizedUpgrade (caps : Dregg2.Authority.Caps) (t : UpgradeTurn) :
    Formula.Holds (truth caps t) source ↔ AuthorizedUpgrade caps t := by
  cases ha : t.auth with
  | byProof v =>
      simp only [source, authorityPrefix, a0, a1, a2, a3, Formula.Holds]
      simp only [truth]
      simp [AuthorizedUpgrade, setProgramAdmissible, ha]
      aesop
  | bySignature =>
      simp only [source, authorityPrefix, a0, a1, a2, a3, Formula.Holds]
      simp only [truth]
      simp [AuthorizedUpgrade, setProgramAdmissible, ha]

def certificate : PublicLiveCertificate 4 := certifyPublic source

theorem optimized_iff_authorizedUpgrade (caps : Dregg2.Authority.Caps) (t : UpgradeTurn) :
    Formula.Holds (truth caps t) certificate.optimized ↔ AuthorizedUpgrade caps t := by
  rw [← source_iff_authorizedUpgrade]
  exact (optimize_holds_iff (truth caps t) source).symm

end UpgradeWorkload

/-! ## 3. Structured credential clearance

Provenance: `Dregg2.Authority.CredentialAttenuation.Clearance.admits`.  The
unconfined/confined-user disjunction is expanded into two branches with the
action-mask and validity-window prefix duplicated.
-/

namespace ClearanceWorkload

open Dregg2.Authority.CredentialAttenuation

def clearancePrefix : Formula 4 := .and (a0) (a1)

def source : Formula 4 :=
  .or (.and clearancePrefix (a2)) (.and clearancePrefix (a3))

def truth (c : Clearance) (r : Request) : Fin 4 → Prop
  | ⟨0, _⟩ => r.action ∈ c.mask
  | ⟨1, _⟩ => c.window.contains r.time
  | ⟨2, _⟩ => c.confined? = false
  | ⟨3, _⟩ => r.user ∈ c.subjects
  | ⟨_, _⟩ => False

/-- Exact all-input equivalence to the structured credential oracle. -/
theorem source_iff_clearance_admits (c : Clearance) (r : Request) :
    Formula.Holds (truth c r) source ↔ c.admits r = true := by
  cases hc : c.confined? with
  | false =>
      simp only [source, clearancePrefix, a0, a1, a2, a3, Formula.Holds]
      simp only [truth]
      simp [Clearance.admits, hc]
      aesop
  | true =>
      simp only [source, clearancePrefix, a0, a1, a2, a3, Formula.Holds]
      simp only [truth]
      simp [Clearance.admits, hc]

def certificate : PublicLiveCertificate 4 := certifyPublic source

theorem optimized_iff_clearance_admits (c : Clearance) (r : Request) :
    Formula.Holds (truth c r) certificate.optimized ↔ c.admits r = true := by
  rw [← source_iff_clearance_admits]
  exact (optimize_holds_iff (truth c r) source).symm

end ClearanceWorkload

/-! ## 4. Stake/vouch strand admission in front of finality

Provenance: `Dregg2.Distributed.StrandAdmission.admitted`, which is consumed by
`finalLeaderAtAdmitted`.  Unlike the three branch-expanded workloads above,
this predicate is already a minimal three-way disjunction.  Its exact
before/after equations deliberately show no optimizer win rather than
manufacturing one.
-/

namespace StrandWorkload

open Dregg2.Authority.Blocklace (AuthorId)
open Dregg2.Distributed.StrandAdmission

def source : Formula 3 := .or (.or (a0) (a1)) (a2)

def truth (fed : AdmissionState) (strand : AuthorId) : Fin 3 → Prop
  | ⟨0, _⟩ => isSeed fed strand = true
  | ⟨1, _⟩ => vouchedToThreshold fed strand = true
  | ⟨2, _⟩ => hasValidBond fed strand = true
  | ⟨_, _⟩ => False

/-- Exact all-input equivalence to the gate that filters finality leaders. -/
theorem source_iff_strand_admitted (fed : AdmissionState) (strand : AuthorId) :
    Formula.Holds (truth fed strand) source ↔ admitted fed strand = true := by
  simp only [source, a0, a1, a2, Formula.Holds]
  simp only [truth]
  simp [admitted, Bool.or_eq_true]

def certificate : PublicLiveCertificate 3 := certifyPublic source

theorem optimized_iff_strand_admitted (fed : AdmissionState) (strand : AuthorId) :
    Formula.Holds (truth fed strand) certificate.optimized ↔ admitted fed strand = true := by
  rw [← source_iff_strand_admitted]
  exact (optimize_holds_iff (truth fed strand) source).symm

end StrandWorkload

/-! ## 5. End-to-end public-descriptor soundness at the atom boundary

The generic live lowering binds every residual input to a public input.  The
following application theorems make the remaining boundary explicit: callers
must show that each public zero-residual means the corresponding production
atom.  Under that hypothesis, any nonempty satisfying trace proves the exact
named DREGG decision.  This does not claim that an atom's arithmetic, hash, or
container implementation was compiled by this Boolean-skeleton module.
-/

theorem public_certificate_sound_of_atoms (hash : List Int → Int) {n : Nat}
    (c : PublicLiveCertificate n) (hcheck : checkPublicLive c = true)
    (truth : Fin n → Prop) (t : VmTrace) (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash (publicDescriptor c.optimized) (fun _ => 0)
      (fun _ => (0, 0)) [] t)
    (hatoms : ∀ a, PublicTruth t.pub a ↔ truth a) :
    Formula.Holds truth c.source := by
  have hpublic := checked_public_statement_sound hash c hcheck t hne hsat
  exact (formula_holds_congr (PublicTruth t.pub) truth hatoms c.source).mp hpublic

namespace AdmissionWorkload

theorem public_descriptor_sound (hash : List Int → Int)
    (ctx : Dregg2.Exec.Admission.AdmCtx) (h : Dregg2.Exec.Admission.TurnHdr)
    (s : Dregg2.Exec.RecChainedState) (t : VmTrace) (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash (publicDescriptor certificate.optimized) (fun _ => 0)
      (fun _ => (0, 0)) [] t)
    (hatoms : ∀ a, PublicTruth t.pub a ↔ truth ctx h s a) :
    Dregg2.Exec.Admission.admissible ctx h s = true := by
  apply (source_iff_admissible ctx h s).mp
  have hs := public_certificate_sound_of_atoms hash certificate
    (checkPublicLive_certify source) (truth ctx h s) t hne hsat hatoms
  simpa [certificate, certifyPublic] using hs

end AdmissionWorkload

namespace UpgradeWorkload

theorem public_descriptor_sound (hash : List Int → Int)
    (caps : Dregg2.Authority.Caps) (u : Dregg2.Upgrade.UpgradeTurn)
    (t : VmTrace) (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash (publicDescriptor certificate.optimized) (fun _ => 0)
      (fun _ => (0, 0)) [] t)
    (hatoms : ∀ a, PublicTruth t.pub a ↔ truth caps u a) :
    Dregg2.Upgrade.AuthorizedUpgrade caps u := by
  apply (source_iff_authorizedUpgrade caps u).mp
  have hs := public_certificate_sound_of_atoms hash certificate
    (checkPublicLive_certify source) (truth caps u) t hne hsat hatoms
  simpa [certificate, certifyPublic] using hs

end UpgradeWorkload

namespace ClearanceWorkload

theorem public_descriptor_sound (hash : List Int → Int)
    (c : Dregg2.Authority.CredentialAttenuation.Clearance)
    (r : Dregg2.Authority.CredentialAttenuation.Request)
    (t : VmTrace) (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash (publicDescriptor certificate.optimized) (fun _ => 0)
      (fun _ => (0, 0)) [] t)
    (hatoms : ∀ a, PublicTruth t.pub a ↔ truth c r a) :
    c.admits r = true := by
  apply (source_iff_clearance_admits c r).mp
  have hs := public_certificate_sound_of_atoms hash certificate
    (checkPublicLive_certify source) (truth c r) t hne hsat hatoms
  simpa [certificate, certifyPublic] using hs

end ClearanceWorkload

namespace StrandWorkload

theorem public_descriptor_sound (hash : List Int → Int)
    (fed : Dregg2.Distributed.StrandAdmission.AdmissionState)
    (strand : Dregg2.Authority.Blocklace.AuthorId)
    (t : VmTrace) (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash (publicDescriptor certificate.optimized) (fun _ => 0)
      (fun _ => (0, 0)) [] t)
    (hatoms : ∀ a, PublicTruth t.pub a ↔ truth fed strand a) :
    Dregg2.Distributed.StrandAdmission.admitted fed strand = true := by
  apply (source_iff_strand_admitted fed strand).mp
  have hs := public_certificate_sound_of_atoms hash certificate
    (checkPublicLive_certify source) (truth fed strand) t hne hsat hatoms
  simpa [certificate, certifyPublic] using hs

end StrandWorkload

/-! ## 6. Exact live DescriptorIR2 ledgers

Counts below distinguish graph equations from the public descriptor's complete
accepting constraint list (one public-input binding per atom, the graph, and
the final `output = 1` equation).  Multiplications are nonlinear
multiplication nodes; widths include the residual inputs and every materialized
auxiliary.  These are definitional computations over the same public
descriptors whose JSON bytes the live certificates seal.
-/

theorem admission_exact_live_ledger :
    (graphConstraints AdmissionWorkload.source).length = 108 ∧
    (graphConstraints AdmissionWorkload.certificate.optimized).length = 58 ∧
    (publicDescriptor AdmissionWorkload.source).constraints.length = 121 ∧
    (publicDescriptor AdmissionWorkload.certificate.optimized).constraints.length = 71 ∧
    (publicDescriptor AdmissionWorkload.certificate.optimized).piCount = 12 ∧
    emittedMultiplications AdmissionWorkload.source = 108 ∧
    emittedMultiplications AdmissionWorkload.certificate.optimized = 58 ∧
    (publicDescriptor AdmissionWorkload.source).traceWidth - 12 = 65 ∧
    (publicDescriptor AdmissionWorkload.certificate.optimized).traceWidth - 12 = 35 ∧
    (publicDescriptor AdmissionWorkload.source).traceWidth = 77 ∧
    (publicDescriptor AdmissionWorkload.certificate.optimized).traceWidth = 47 := by
  decide

theorem admission_optimized_shape :
    AdmissionWorkload.certificate.optimized =
      .and AdmissionWorkload.common (.or (a3) (a4)) := by
  decide

theorem upgrade_exact_live_ledger :
    (graphConstraints UpgradeWorkload.source).length = 28 ∧
    (graphConstraints UpgradeWorkload.certificate.optimized).length = 18 ∧
    (publicDescriptor UpgradeWorkload.source).constraints.length = 33 ∧
    (publicDescriptor UpgradeWorkload.certificate.optimized).constraints.length = 23 ∧
    (publicDescriptor UpgradeWorkload.certificate.optimized).piCount = 4 ∧
    emittedMultiplications UpgradeWorkload.source = 28 ∧
    emittedMultiplications UpgradeWorkload.certificate.optimized = 18 ∧
    (publicDescriptor UpgradeWorkload.source).traceWidth - 4 = 17 ∧
    (publicDescriptor UpgradeWorkload.certificate.optimized).traceWidth - 4 = 11 ∧
    (publicDescriptor UpgradeWorkload.source).traceWidth = 21 ∧
    (publicDescriptor UpgradeWorkload.certificate.optimized).traceWidth = 15 := by
  decide

theorem upgrade_optimized_shape :
    UpgradeWorkload.certificate.optimized =
      .and UpgradeWorkload.authorityPrefix (.or (a2) (a3)) := by
  decide

theorem clearance_exact_live_ledger :
    (graphConstraints ClearanceWorkload.source).length = 28 ∧
    (graphConstraints ClearanceWorkload.certificate.optimized).length = 18 ∧
    (publicDescriptor ClearanceWorkload.source).constraints.length = 33 ∧
    (publicDescriptor ClearanceWorkload.certificate.optimized).constraints.length = 23 ∧
    (publicDescriptor ClearanceWorkload.certificate.optimized).piCount = 4 ∧
    emittedMultiplications ClearanceWorkload.source = 28 ∧
    emittedMultiplications ClearanceWorkload.certificate.optimized = 18 ∧
    (publicDescriptor ClearanceWorkload.source).traceWidth - 4 = 17 ∧
    (publicDescriptor ClearanceWorkload.certificate.optimized).traceWidth - 4 = 11 ∧
    (publicDescriptor ClearanceWorkload.source).traceWidth = 21 ∧
    (publicDescriptor ClearanceWorkload.certificate.optimized).traceWidth = 15 := by
  decide

theorem clearance_optimized_shape :
    ClearanceWorkload.certificate.optimized =
      .and ClearanceWorkload.clearancePrefix (.or (a2) (a3)) := by
  decide

theorem strand_exact_live_ledger :
    (graphConstraints StrandWorkload.source).length = 13 ∧
    (graphConstraints StrandWorkload.certificate.optimized).length = 13 ∧
    (publicDescriptor StrandWorkload.source).constraints.length = 17 ∧
    (publicDescriptor StrandWorkload.certificate.optimized).constraints.length = 17 ∧
    (publicDescriptor StrandWorkload.certificate.optimized).piCount = 3 ∧
    emittedMultiplications StrandWorkload.source = 13 ∧
    emittedMultiplications StrandWorkload.certificate.optimized = 13 ∧
    (publicDescriptor StrandWorkload.source).traceWidth - 3 = 8 ∧
    (publicDescriptor StrandWorkload.certificate.optimized).traceWidth - 3 = 8 ∧
    (publicDescriptor StrandWorkload.source).traceWidth = 11 ∧
    (publicDescriptor StrandWorkload.certificate.optimized).traceWidth = 11 := by
  decide

theorem strand_already_normal_shape :
    StrandWorkload.certificate.optimized = StrandWorkload.source := by
  decide

/-! ## 7. Fail-closed byte and layout gates -/

#guard checkPublicLive AdmissionWorkload.certificate
#guard checkPublicLive UpgradeWorkload.certificate
#guard checkPublicLive ClearanceWorkload.certificate
#guard checkPublicLive StrandWorkload.certificate

def admissionBadBytes : PublicLiveCertificate 12 :=
  { AdmissionWorkload.certificate with
    descriptorBytes := AdmissionWorkload.certificate.descriptorBytes ++ " " }

def upgradeBadLayout : PublicLiveCertificate 4 :=
  { UpgradeWorkload.certificate with
    layout := { UpgradeWorkload.certificate.layout with traceWidth := 0 } }

def clearanceBadEndpoint : PublicLiveCertificate 4 :=
  { ClearanceWorkload.certificate with optimized := ClearanceWorkload.source }

def strandBadVersion : PublicLiveCertificate 3 :=
  { StrandWorkload.certificate with version := publicLiveVersion + 1 }

#guard !checkPublicLive admissionBadBytes
#guard !checkPublicLive upgradeBadLayout
#guard !checkPublicLive clearanceBadEndpoint
#guard !checkPublicLive strandBadVersion

theorem admission_bytes_exact :
    AdmissionWorkload.certificate.descriptorBytes =
      Dregg2.Circuit.DescriptorIR2.emitVmJson2
        (publicDescriptor AdmissionWorkload.certificate.optimized) := by
  exact (checkPublicLive_spec AdmissionWorkload.certificate |>.mp
    (checkPublicLive_certify AdmissionWorkload.source)).2.2.2.2.2

theorem upgrade_layout_exact :
    UpgradeWorkload.certificate.layout =
      publicLayoutOf UpgradeWorkload.certificate.optimized := by
  exact (checkPublicLive_spec UpgradeWorkload.certificate |>.mp
    (checkPublicLive_certify UpgradeWorkload.source)).2.2.2.2.1

theorem clearance_bytes_exact :
    ClearanceWorkload.certificate.descriptorBytes =
      Dregg2.Circuit.DescriptorIR2.emitVmJson2
        (publicDescriptor ClearanceWorkload.certificate.optimized) := by
  exact (checkPublicLive_spec ClearanceWorkload.certificate |>.mp
    (checkPublicLive_certify ClearanceWorkload.source)).2.2.2.2.2

theorem strand_layout_exact :
    StrandWorkload.certificate.layout =
      publicLayoutOf StrandWorkload.certificate.optimized := by
  exact (checkPublicLive_spec StrandWorkload.certificate |>.mp
    (checkPublicLive_certify StrandWorkload.source)).2.2.2.2.1

#assert_all_clean [
  AdmissionWorkload.source_iff_admissible,
  AdmissionWorkload.optimized_iff_admissible,
  UpgradeWorkload.source_iff_authorizedUpgrade,
  UpgradeWorkload.optimized_iff_authorizedUpgrade,
  ClearanceWorkload.source_iff_clearance_admits,
  ClearanceWorkload.optimized_iff_clearance_admits,
  StrandWorkload.source_iff_strand_admitted,
  StrandWorkload.optimized_iff_strand_admitted,
  public_certificate_sound_of_atoms,
  AdmissionWorkload.public_descriptor_sound,
  UpgradeWorkload.public_descriptor_sound,
  ClearanceWorkload.public_descriptor_sound,
  StrandWorkload.public_descriptor_sound,
  admission_exact_live_ledger,
  admission_optimized_shape,
  upgrade_exact_live_ledger,
  upgrade_optimized_shape,
  clearance_exact_live_ledger,
  clearance_optimized_shape,
  strand_exact_live_ledger,
  strand_already_normal_shape,
  admission_bytes_exact,
  upgrade_layout_exact,
  clearance_bytes_exact,
  strand_layout_exact
]

end Dregg2.Metatheory.DirectLogicDreggWorkloads

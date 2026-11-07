/-
# Dregg2.Apps.StorageGatewayMandateGated — storage gateway mandate on `execFullForestG` / `trajG`.
-/
import Dregg2.Exec.GatedForestCfg
import Dregg2.Exec.CellExecutor
import Dregg2.Exec.CellReal
import Dregg2.Apps.StorageGatewayMandate
import Dregg2.Verify.Catalog
import Dregg2.Verify.Contract

namespace Dregg2.Apps.StorageGatewayMandateGated

open Dregg2.Exec
open Dregg2.Exec (cellObsA trajG SchedG)
open Dregg2.Apps.StorageGatewayMandate
open Dregg2.Verify (gateRevoked asset_conserved_forever_production assetConserved composeContracts)
open Dregg2.Verify.Production (Contract Sched liftFromKernelForest)

abbrev KFContract := Dregg2.Verify.KernelForest.Contract
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Exec.EffectsState
open Dregg2.Exec.FullForestAuth
open Dregg2.Exec.StarbridgeGated
open Dregg2.Exec.StarbridgeGated

abbrev sgmActor : CellId := mandateActor

def sgmSetKeyNode (cred : Authorization Dg Pf) (key : Int) : DForest :=
  ⟨ mkAuth cred [], .setFieldA sgmActor mandateCell objectKeySlot key, [] ⟩

def sgmSetOpNode (cred : Authorization Dg Pf) (op : Int) : DForest :=
  ⟨ mkAuth cred [], .setFieldA sgmActor mandateCell lastOpSlot op, [] ⟩

def sgmDebitVolumeNode (cred : Authorization Dg Pf) (newSpent : Int) : DForest :=
  ⟨ mkAuth cred [], .setFieldA sgmActor mandateCell volumeSpentSlot newSpent, [] ⟩

def sgmEmitNode (cred : Authorization Dg Pf) (blobHash : Int) : DForest :=
  ⟨ mkAuth cred [], .emitEventA sgmActor mandateCell sgmEmitTopic blobHash, [] ⟩

/-- Gated PUT turn: set object key + op, emit blob hash. -/
def sgmPutNode (cred : Authorization Dg Pf) (key op blobHash : Int) : DForest :=
  ⟨ mkAuth cred [], .setFieldA sgmActor mandateCell objectKeySlot key
  , [ { holder := sgmActor, keep := [], parentCap := .endpoint sgmActor []
      , sub := ⟨ mkAuth cred [], .setFieldA sgmActor mandateCell lastOpSlot op
              , [ { holder := sgmActor, keep := [], parentCap := .endpoint sgmActor []
                  , sub := ⟨ mkAuth cred [], .emitEventA sgmActor mandateCell sgmEmitTopic blobHash, [] ⟩ } ] ⟩ } ] ⟩

theorem execFullForestG_leaf (s : RecChainedState) (na : DNodeAuth) (a : FullActionA) :
    execFullForestG s (⟨na, a, []⟩ : DForest) = execFullAGated s na a := by
  show (match execFullAGated s na a with
        | some s' => execFullChildrenG (targetOf a) s' ([] : List DChild)
        | none    => none) = execFullAGated s na a
  cases execFullAGated s na a with
  | none   => rfl
  | some _ => rfl

theorem gateOK_forged_false (s : RecChainedState) : gateOK (mkAuth forgedCred []) s = false := by
  have hcred : credentialValidG (mkAuth forgedCred []) = false := by decide
  unfold gateOK; rw [hcred]; simp

theorem sgm_forged_rejected (s : RecChainedState) (key : Int) :
    execFullForestG s (sgmSetKeyNode forgedCred key) = none := by
  rw [sgmSetKeyNode]
  exact execFullForestG_unauthorized_fails s (mkAuth forgedCred [])
    (.setFieldA sgmActor mandateCell objectKeySlot key) [] (gateOK_forged_false s)

theorem sgm_forged_put_rejected (s : RecChainedState) (key op blobHash : Int) :
    execFullForestG s (sgmPutNode forgedCred key op blobHash) = none := by
  rw [sgmPutNode]
  exact execFullForestG_unauthorized_fails s (mkAuth forgedCred [])
    (.setFieldA sgmActor mandateCell objectKeySlot key) [] (gateOK_forged_false s)

theorem sgm_revoked_rejected (s : RecChainedState) (cred : Authorization Dg Pf) (key : Int)
    (hrev : s.kernel.revoked.contains (mkAuth cred []).credNul = true) :
    execFullForestG s (sgmSetKeyNode cred key) = none := by
  rw [sgmSetKeyNode]
  exact execFullForestG_unauthorized_fails s (mkAuth cred [])
    (.setFieldA sgmActor mandateCell objectKeySlot key) [] (gateOK_revoked_fails (mkAuth cred []) s hrev)

theorem sgm_over_debit_rejected_gated (s : RecChainedState) (newSpent : Int)
    (hgate : gateOK (mkAuth goodCred []) s = true)
    (hbound : caveatsAdmit s.kernel volumeSpentSlot sgmActor mandateCell newSpent = false) :
    execFullForestG s (sgmDebitVolumeNode goodCred newSpent) = none := by
  rw [sgmDebitVolumeNode, execFullForestG_leaf, execFullAGated, if_pos hgate]
  exact stateStepDev_caveat_violation_fails s volumeSpentSlot sgmActor mandateCell newSpent hbound

/-! ### §commit-iff — the gated executor COMMITS a `last_op` write IFF `sgmAdmitM`'s op-leg admits.

The output-side value frame for the op leg: on a mandate cell carrying `mandateCaveats`, with valid
prior op code, the GATED executor commits a `last_op := op` write IFF the gate passes AND the op is
admitted by `sgmAdmitM`'s op-allowlist ∧ GET-clearance leg. The negative tooth
(`sgm_guest_get_rejected`) exhibits a concrete guest (no-clearance) state where a GET write is
rejected by the executor. -/

theorem execFullForestG_setOpNode (s : RecChainedState) (cred : Authorization Dg Pf) (op : Int) :
    execFullForestG s (sgmSetOpNode cred op)
      = (if gateOK (mkAuth cred []) s = true
         then stateStepGuarded s lastOpSlot sgmActor mandateCell op
         else none) := by
  rw [sgmSetOpNode, execFullForestG_leaf, execFullAGated]
  rfl

/-- **`sgm_commit_iff_op_admit_gated` (output-side COMMIT-IFF-ADMIT, op leg).** On a mandate
cell carrying the op admit-table, with the credential gate (`hg`) and the executor's authority/liveness
gate (`hauth`) passing, the gated executor COMMITS a `last_op := op.toInt` write IFF `sgmAdmitM`'s op
leg admits `op`. Pins that the ONLY committable ops are the admitted ones. -/
theorem sgm_commit_iff_op_admit_gated (s : RecChainedState)
    (hprog : s.kernel.slotCaveats mandateCell = mandateCaveats) (op : StorageOp)
    (hold : fieldOf lastOpSlot (s.kernel.cell mandateCell) ∈ [(-1 : Int), 0, 1, 2])
    (hg : gateOK (mkAuth goodCred []) s = true)
    (hauth : stateAuthB s.kernel.caps sgmActor mandateCell = true ∧ mandateCell ∈ s.kernel.accounts
              ∧ cellLive s.kernel mandateCell = true) :
    (∃ s', execFullForestG s (sgmSetOpNode goodCred op.toInt) = some s')
      ↔ sgmOpAdmitted demoMandate op = true := by
  rw [execFullForestG_setOpNode, if_pos hg]
  constructor
  · rintro ⟨s', hs'⟩
    have hadm := stateStepGuarded_admits hs'
    exact (sgm_commit_iff_op_admit s.kernel hprog sgmActor op hold).mp hadm
  · intro hadm
    have hcav : caveatsAdmit s.kernel lastOpSlot sgmActor mandateCell op.toInt = true :=
      (sgm_commit_iff_op_admit s.kernel hprog sgmActor op hold).mpr hadm
    refine ⟨{ kernel := writeField s.kernel lastOpSlot mandateCell (.int op.toInt),
              log := { actor := sgmActor, src := mandateCell, dst := mandateCell, amt := 0 } :: s.log }, ?_⟩
    unfold stateStepGuarded
    rw [if_pos hcav]
    unfold stateStep
    rw [if_pos hauth]

/-! ### §negative-tooth — a GUEST writing op GET (no clearance) is rejected by the EXECUTOR. -/

/-- Guest-clearance program: the op admit-table built from `guestMandate` (no GET clearance) — admits
PUT/LIST but NOT GET. -/
def guestCaveats : List SlotCaveat :=
  [ .immutable commitmentAnchorSlot
  , .monotonic volumeSpentSlot
  , .boundedBy volumeSpentSlot 0 (demoMandate.volumeBudget.ceiling : Int)
  , .admitTable lastOpSlot (sgmOpAdmitTable guestMandate) ]

/-- Genesis cell carrying the GUEST (no-GET-clearance) op program. -/
def guestSgmG0 : RecChainedState :=
  { kernel :=
      { accounts := {0}
        cell := fun c =>
          if c = mandateCell then
            .record [("balance", .int 0), (objectKeySlot, .int 0), (lastOpSlot, .int (-1)),
                     (volumeSpentSlot, .int 0), (commitmentAnchorSlot, .int demoMandate.anchor)]
          else .record [("balance", .int 0)]
        caps := fun _ => []
        bal := fun c a => if c = 0 then (if a = 0 then 100 else if a = 1 then 7 else 0) else 0
        slotCaveats := fun c => if c = mandateCell then guestCaveats else [] }
    log := [] }

/-- **`sgm_guest_get_rejected` (THE NEGATIVE TOOTH).** A guest lacking GET clearance CANNOT
record a GET op (`last_op := 0`): the executor returns `none`, because `(_, 0)` is NOT in the guest's
op admit-table. This is exactly the request `sgmAdmitM guestMandate _ {op := GET}` rejects — now
ENFORCED BY THE EXECUTOR (where no prior caveat could express clearance). -/
theorem sgm_guest_get_rejected :
    execFullForestG guestSgmG0 (sgmSetOpNode goodCred (StorageOp.GET.toInt)) = none := by
  rw [execFullForestG_setOpNode]
  by_cases hg : gateOK (mkAuth goodCred []) guestSgmG0 = true
  · rw [if_pos hg]
    have hcav : caveatsAdmit guestSgmG0.kernel lastOpSlot sgmActor mandateCell (StorageOp.GET.toInt) = false := by decide
    exact stateStepDev_caveat_violation_fails guestSgmG0 lastOpSlot sgmActor mandateCell (StorageOp.GET.toInt) hcav
  · rw [if_neg (by simp [hg])]

theorem sgmSetKeyNode_delta_zero (cred : Authorization Dg Pf) (key : Int) (b : AssetId) :
    turnLedgerDeltaAsset ((lowerForestG (sgmSetKeyNode cred key)).map Prod.snd) b = 0 := by
  simp [sgmSetKeyNode, lowerForestG, lowerChildrenG, turnLedgerDeltaAsset, ledgerDeltaAsset]

theorem sgmEmitNode_delta_zero (cred : Authorization Dg Pf) (blobHash : Int) (b : AssetId) :
    turnLedgerDeltaAsset ((lowerForestG (sgmEmitNode cred blobHash)).map Prod.snd) b = 0 := by
  simp [sgmEmitNode, lowerForestG, lowerChildrenG, turnLedgerDeltaAsset, ledgerDeltaAsset]

theorem sgm_op_conserves (s s' : RecChainedState) (cred : Authorization Dg Pf) (key : Int) (b : AssetId)
    (h : execFullForestG s (sgmSetKeyNode cred key) = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b :=
  execFullForestG_conserves_per_asset s s' (sgmSetKeyNode cred key) b h
    (sgmSetKeyNode_delta_zero cred key b)

theorem sgm_emit_conserves (s s' : RecChainedState) (cred : Authorization Dg Pf) (blobHash : Int) (b : AssetId)
    (h : execFullForestG s (sgmEmitNode cred blobHash) = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b :=
  execFullForestG_conserves_per_asset s s' (sgmEmitNode cred blobHash) b h
    (sgmEmitNode_delta_zero cred blobHash b)

theorem sgm_pay_conserved_forever (s0 : RecChainedState) (sched : SchedG) :
    ∀ n, cellObsA (trajG s0 sched n) payAsset = cellObsA s0 payAsset :=
  asset_conserved_forever_production s0 payAsset sched

theorem sgm_revoked_rejected_forever (s : RecChainedState) (cred : Authorization Dg Pf) (key : Int)
    (hinit : (mkAuth cred []).credNul ∈ s.kernel.revoked) (sched : SchedG) :
    ∀ n, execFullForestG (trajG s sched n) (sgmSetKeyNode cred key) = none := by
  intro n
  exact sgm_revoked_rejected (trajG s sched n) cred key
    (List.contains_iff_mem.mpr ((gateRevoked (mkAuth cred []).credNul).forever hinit sched n))

noncomputable def sgmStepLegalContractKF : KFContract where
  Inv s := sgmWF s.kernel
  step_ob a cf h := by
    erw [CellExecutor.kernelForest_next_eq]; unfold cellNextA
    cases hc : execFullForestA a cf.1 with
    | none => simp only [Option.getD_none]; exact h
    | some a' => simp only [Option.getD_some]; exact sgmWF_traj_carries a a' cf.1 hc h
  shape := .other

noncomputable def sgmStepLegalContract : Contract := liftFromKernelForest sgmStepLegalContractKF

noncomputable def sgmPayConserved (s0 : RecChainedState) : Contract := assetConserved s0 payAsset
noncomputable def sgmRevokedDead (nul : Nat) : Contract := gateRevoked nul

/-- **`sgmSafetyContract`** — the unconditional-carry legs (step-legal program-live + pay conserved +
revoked-dead). The genuine bucket binding `sgmInBucket` (which pins the anchor value) is NOT a contract
leg: its `sgmAnchor = bucket` conjunct is breakable by a `makeSovereign` aimed at the mandate cell, so it
cannot satisfy the contract's EVERY-step `step_ob`. It is carried separately by the anchor-safe induction
`sgm_bucket_strong_forever` and threaded into `sgm_safety_forever`. -/
noncomputable def sgmSafetyContract (s0 : RecChainedState) (nul : Nat) : Contract :=
  composeContracts (composeContracts sgmStepLegalContract (sgmPayConserved s0)) (sgmRevokedDead nul)

open Dregg2.Exec (cellNextG conservingGated_erase)
open Dregg2.Exec.StarbridgeGated (eraseForestG execForestG execForestG_erases)

/-- A gated schedule is anchor-safe for the mandate cell iff every erased forest it issues is. -/
def SchedAnchorSafe (sched : SchedG) : Prop :=
  ∀ n, anchorForestOK mandateCell (eraseForestG (sched n).val)

/-- **`sgmStrong_cellNextG_carries`** — one anchor-safe gated step preserves the conjunction
`mandateCell live ∧ sgmInBucketStrong`. Bridges `cellNextG` to `execFullForestA` via the erase. -/
theorem sgmStrong_cellNextG_carries (bucket : Int) (s : RecChainedState) (cg : ConservingGatedForest)
    (hok : anchorForestOK mandateCell (eraseForestG cg.val))
    (hinv : mandateCell ∈ s.kernel.accounts ∧ sgmInBucketStrong s.kernel bucket) :
    mandateCell ∈ (cellNextG s cg).kernel.accounts ∧ sgmInBucketStrong (cellNextG s cg).kernel bucket := by
  obtain ⟨hlive, hstrong⟩ := hinv
  unfold cellNextG
  cases hc : execForestG s cg.val with
  | none => simp only [Option.getD_none]; exact ⟨hlive, hstrong⟩
  | some s' =>
      simp only [Option.getD_some]
      have hfa : execFullForestA s (eraseForestG cg.val) = some s' := execForestG_erases s s' cg.val hc
      have hokE : anchorForestOK mandateCell (eraseForestG cg.val) := hok
      have hstrong' := sgmBucketStrong_traj_carries s s' (eraseForestG cg.val) bucket hfa hstrong hokE hlive
      refine ⟨?_, hstrong'⟩
      -- liveness persists (the program-live frame again)
      exact (execFullForestA_progLive_preserved s s' (eraseForestG cg.val) mandateCell mandateCaveats
        hfa hlive hstrong.2).1

/-- **`sgm_bucket_strong_forever` — VALUE-PINNING CROWN LEG.** Along EVERY anchor-safe gated
schedule, the agent stays in the SPECIFIC bucket: `sgmAnchor (trajG …) = bucket` (the literal binding),
not merely "some program is live". This is the strong predicate wired onto the living trajectory. -/
theorem sgm_bucket_strong_forever (bucket : Int) (s : RecChainedState)
    (hlive : mandateCell ∈ s.kernel.accounts) (hstrong : sgmInBucketStrong s.kernel bucket)
    (sched : SchedG) (hsafe : SchedAnchorSafe sched) :
    ∀ n, mandateCell ∈ (trajG s sched n).kernel.accounts
          ∧ sgmInBucketStrong (trajG s sched n).kernel bucket := by
  intro n
  induction n with
  | zero => exact ⟨hlive, hstrong⟩
  | succ k ih =>
      show mandateCell ∈ (cellNextG (trajG s sched k) (sched k)).kernel.accounts
            ∧ sgmInBucketStrong (cellNextG (trajG s sched k) (sched k)).kernel bucket
      exact sgmStrong_cellNextG_carries bucket (trajG s sched k) (sched k) (hsafe k) ih

/-- **`sgm_safety_forever` — the per-app PRODUCTION CROWN with the GENUINE bucket binding.**
Along every anchor-safe `trajG`: the mandate stays step-legal/program-live (`sgmWF`), pay is conserved,
the revoked credential stays dead, AND the agent stays in the SPECIFIC bucket `bucket` —
`sgmInBucket (trajG …) bucket`, whose `sgmAnchor = bucket` conjunct genuinely pins the tag. The first
three legs ride the unconditional `sgmSafetyContract`; the genuine bucket leg rides the anchor-safe
induction `sgm_bucket_strong_forever`. The `SchedAnchorSafe` hypothesis is the precise, stated residual:
the ONE behaviour (`makeSovereign` aimed at the cell) the immutable-anchor caveat cannot reject inline. -/
theorem sgm_safety_forever (s0 : RecChainedState) (nul : Nat) (bucket : Int) (s : RecChainedState)
    (hstep : sgmWF s.kernel) (hpay : cellObsA s payAsset = cellObsA s0 payAsset)
    (hrev : nul ∈ s.kernel.revoked) (hbucket : sgmInBucket s.kernel bucket)
    (sched : SchedG) (hsafe : SchedAnchorSafe sched) :
    ∀ n,
      sgmWF (trajG s sched n).kernel ∧
        cellObsA (trajG s sched n) payAsset = cellObsA s0 payAsset ∧
          nul ∈ (trajG s sched n).kernel.revoked ∧
            sgmInBucket (trajG s sched n).kernel bucket := by
  intro n
  obtain ⟨hlive, hprog, hanchor⟩ := hbucket
  have h := (sgmSafetyContract s0 nul).forever
    (And.intro (And.intro hstep hpay) hrev) sched n
  rcases h with ⟨⟨hstep', hpay'⟩, hrev'⟩
  obtain ⟨hlive', hanchor', hprog'⟩ :=
    sgm_bucket_strong_forever bucket s hlive ⟨hanchor, hprog⟩ sched hsafe n
  exact And.intro hstep' (And.intro hpay' (And.intro hrev' ⟨hlive', hprog', hanchor'⟩))

/-! ### §strong-teeth — the value-pinning predicate is NON-VACUOUS: drift REJECTED, honest ADMITTED. -/

def sgmG0 : RecChainedState :=
  { kernel :=
      { accounts := {0}
        cell := fun c =>
          if c = mandateCell then
            .record [("balance", .int 0), (objectKeySlot, .int 0), (lastOpSlot, .int (-1)),
                     (volumeSpentSlot, .int 0), (commitmentAnchorSlot, .int demoMandate.anchor)]
          else .record [("balance", .int 0)]
        caps := fun _ => []
        bal := fun c a => if c = 0 then (if a = 0 then 100 else if a = 1 then 7 else 0) else 0
        slotCaveats := fun c => if c = mandateCell then mandateCaveats else [] }
    log := [] }

/-- A drifted genesis: anchor rebound to a DIFFERENT bucket value (`demoMandate.anchor + 1`). -/
def sgmDriftCell : CellId → Value := fun c =>
  if c = mandateCell then
    .record [("balance", .int 0), (objectKeySlot, .int 0), (lastOpSlot, .int (-1)),
             (volumeSpentSlot, .int 0), (commitmentAnchorSlot, .int (demoMandate.anchor + 1))]
  else .record [("balance", .int 0)]

def sgmDriftG0 : RecChainedState :=
  { sgmG0 with kernel := { sgmG0.kernel with cell := sgmDriftCell } }

def sgmGPutKey : Option RecChainedState :=
  execFullForestG sgmG0 (sgmSetKeyNode goodCred demoKeyCode)

def sgmGPutOp : Option RecChainedState :=
  sgmGPutKey.bind (fun s => execFullForestG s (sgmSetOpNode goodCred (StorageOp.PUT.toInt)))

def sgmGPutEmit : Option RecChainedState :=
  sgmGPutOp.bind (fun s => execFullForestG s (sgmEmitNode goodCred demoBlobHash))

-- VALUE-PINNING NON-VACUITY: honest in-bucket genesis ADMITTED; drifted anchor REJECTED.
#guard (sgmInBucketStrong sgmG0.kernel (demoMandate.anchor : Int))                          -- TRUE
#guard (sgmInBucketStrong sgmDriftG0.kernel (demoMandate.anchor : Int)) == false            -- drift REJECTED
#guard (sgmAnchor sgmDriftG0.kernel == sgmAnchor sgmG0.kernel) == false                     -- anchors differ
#guard (sgmInBucketStrong sgmDriftG0.kernel (demoMandate.anchor + 1 : Int))                 -- drift IS in its own bucket
-- GENUINE BINDING NON-VACUITY (the crown predicate itself, both poles): the in-bucket predicate now
-- USES its `bucket` tag — it ACCEPTS the correctly-tagged state and REJECTS the wrong tag.
#guard (decide (sgmInBucket sgmG0.kernel (demoMandate.anchor : Int)))                       -- right tag ACCEPTED  (not False)
#guard (decide (sgmInBucket sgmG0.kernel (demoMandate.anchor + 1 : Int))) == false          -- wrong tag REJECTED  (not True)
#guard (decide (sgmInBucket sgmDriftG0.kernel (demoMandate.anchor : Int))) == false         -- drifted anchor REJECTED at the bound tag

#guard (gateOK (mkAuth goodCred []) sgmG0)
#guard (sgmAdmitM demoMandate (SgmRuntime.init demoMandate) demoPutReq).isSome
#guard (sgmAdmitM demoMandate (SgmRuntime.init demoMandate) demoBadPutReq).isSome == false
#guard (sgmAdmitM guestMandate (SgmRuntime.init guestMandate) demoGetReq).isSome == false
#guard (caveatsAdmit sgmG0.kernel volumeSpentSlot sgmActor mandateCell 11) == false
#guard ((execFullForestG sgmG0 (sgmDebitVolumeNode goodCred 11)).isSome) == false
#guard ((execFullForestG sgmG0 (sgmSetKeyNode forgedCred demoKeyCode)).isSome) == false
#guard ((execFullForestG ({ sgmG0 with kernel := { sgmG0.kernel with revoked := [(mkAuth goodCred []).credNul] } })
          (sgmSetKeyNode goodCred demoKeyCode)).isSome) == false
#guard (sgmGPutKey.map (fun s => fieldOf objectKeySlot (s.kernel.cell mandateCell))) == some demoKeyCode
#guard (sgmGPutOp.map (fun s => fieldOf lastOpSlot (s.kernel.cell mandateCell))) == some 1
#guard (sgmGPutEmit.isSome)
#guard (sgmVolumeBound sgmG0.kernel)
#guard (sgmAnchorIs sgmG0.kernel (demoMandate.anchor : Int))
#guard ((sgmGPutEmit.map (fun s => recTotalAsset s.kernel payAsset)).getD 0) == 100

-- COMMIT-IFF-ADMIT negative tooth: a guest lacking GET clearance cannot record a GET op — the
-- EXECUTOR rejects the `last_op := 0` write (where no prior caveat could express clearance).
#guard ((execFullForestG guestSgmG0 (sgmSetOpNode goodCred (StorageOp.GET.toInt))).isSome) == false
#guard (caveatsAdmit guestSgmG0.kernel lastOpSlot sgmActor mandateCell (StorageOp.GET.toInt)) == false
-- the demo (writer-clearance) cell DOES admit the GET op
#guard (caveatsAdmit sgmG0.kernel lastOpSlot sgmActor mandateCell (StorageOp.GET.toInt)) == true
#guard (sgmOpAdmitted demoMandate StorageOp.GET) == true
#guard (sgmOpAdmitted guestMandate StorageOp.GET) == false
#guard (sgmOpAdmitted demoMandate StorageOp.PUT) == true

#assert_axioms execFullForestG_setOpNode
#assert_axioms sgm_commit_iff_op_admit_gated
#assert_axioms sgm_guest_get_rejected
#assert_axioms execFullForestG_leaf
#assert_axioms sgm_forged_rejected
#assert_axioms sgm_revoked_rejected
#assert_axioms sgm_over_debit_rejected_gated
#assert_axioms sgm_op_conserves
#assert_axioms sgm_pay_conserved_forever
#assert_axioms sgm_revoked_rejected_forever
#assert_axioms sgmSafetyContract
#assert_axioms sgm_safety_forever
#assert_axioms sgmStrong_cellNextG_carries
#assert_axioms sgm_bucket_strong_forever

end Dregg2.Apps.StorageGatewayMandateGated
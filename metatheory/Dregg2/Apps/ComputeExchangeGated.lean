/-
# Dregg2.Apps.ComputeExchangeGated — a VALUE-MOVING compute market as a VERIFIED USERSPACE APP,
RE-POINTED onto the REAL escrow FACTORY (F1b: the kernel escrow verbs are GONE).

A compute exchange is the canonical pay-for-work escrow workflow: a BUYER locks the job payment, the
PROVIDER receives it on delivery, or the buyer gets it back on failure. This app is RE-POINTED off the
off-ledger escrow VERB family (`createEscrowA`/`releaseEscrowA`/`refundEscrowA` over the deleted
`escrows` side-table) onto the FACTORY-BORN escrow CELL: the locked payment is held in the escrow
cell's OWN per-asset `bal` column, the lifecycle lives in a SLOT governed by the factory's installed
state machine `admitTable [(open,released),(open,refunded)]`, and conservation is the ORDINARY
per-asset move law — NO side-table. (`Dregg2.Apps.EscrowFactory` is the factory; this app
instantiates it, exactly as `Apps/BountyBoardGated.lean` does for the bounty shape.)

## The ops (re-pointed)

  * **order**  — mint a factory escrow cell (`createCellFromFactoryA` ⇒ `EscrowFactory.mintEscrowCell`)
    carrying the deal terms + state machine, then FUND it with an ordinary move of the payment into the
    cell's `bal` column (`EscrowFactory.depositEscrow`). Conservation-neutral mint + conserving move.
  * **settle** — RELEASE the held payment to the provider (`EscrowFactory.releaseEscrow`): the
    OPEN→RELEASED transition + move `bal` out, gated on the delivery-condition witness.
  * **refund** — REFUND the held payment to the buyer (`EscrowFactory.refundEscrow`): OPEN→REFUNDED.

## The gate teeth (preserved) + the settle-safety contract (re-proved on the factory shape)

  1. `cx_forged_rejected`               — a FORGED credential on ANY gated op ⇒ `none`, ∀ s;
  2. `cx_revoked_rejected`              — a credential whose nullifier is in `s.kernel.revoked` ⇒ `none`;
  3. `cx_order_mint_conserves`          — minting the factory escrow cell is conservation-neutral;
  4. `cx_order_fund_conserves`          — funding it (the payment move) conserves every asset;
  5. `cx_settle_conserves`              — a committed settle (release) conserves every asset;
  6. `cx_refund_conserves`              — a committed refund conserves every asset;
  7. `cx_no_double_resolve`             — once settled, neither a second settle nor a refund commits;
  8. `cx_settle_requires_condition`     — a settle with a wrong delivery witness is rejected;
  9. `cx_settle_requires_live_provider` — D3: a settle into a non-account provider is rejected;
 10. `cx_refund_requires_live_buyer`    — D3: a refund into a non-account buyer is rejected;
 11. `cx_open_settleable`/`cx_open_refundable` — value-not-stranded: a funded OPEN job resolves.

## App-level semantics (Hatchery bridge — §8b, PRESERVED across the re-point)

  * `cx_pay_conserved_forever` — payment supply never drifts on `trajG` (Tier-4 `conservation%`);
  * `cx_revoked_rejected_forever` — a revoked market participant cannot order/settle/refund, ever;
  * `cx_revoked_pay_safety_forever` — composed Identity revocation + payment conservation
    (`CellContract.composeContracts` / `revokedPaySafety` in `Verify/Contract.lean`).
-/
import Dregg2.Exec.GatedForestCfg
import Dregg2.Exec.CellExecutor
import Dregg2.Exec.CellReal
import Dregg2.Verify.Catalog
import Dregg2.Verify.Contract
import Dregg2.Apps.EscrowFactory

namespace Dregg2.Apps.ComputeExchangeGated

open Dregg2.Exec
open Dregg2.Exec (cellObsA trajG SchedG)
open Dregg2.Verify (gateRevoked asset_conserved_forever_production assetConserved
  revoked_pay_safety_forever)
open Dregg2.Verify.Production (Contract Sched)
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Exec.FullForestAuth
open Dregg2.Exec.StarbridgeGated
open Dregg2.Authority (Cap)
open Dregg2.Apps.EscrowFactory
open Dregg2.Verify.EscrowFactoryProbe

/-! ## §1 — The compute-market DOMAIN at the Demo carriers (buyer, provider, the job's payment). -/

/-- The BUYER cell (orders the job, funds the escrow cell, the refund target). -/
abbrev buyer : CellId := 0
/-- The PROVIDER cell (delivers the job, the settle target). The D3 settle-liveness gate checks THIS
cell is a live account before paying it. -/
abbrev provider : CellId := 1
/-- The payment asset class (the currency the job is priced in). -/
abbrev payAsset : AssetId := 0
/-- The job id (kept for vocabulary continuity with the verb-era market; the factory key is `cxVk`). -/
abbrev jobId : Nat := 42
/-- The factory key the market's escrow factory is published at. -/
abbrev cxVk : Int := 7
/-- The fresh escrow cell the factory mints for this job. -/
abbrev escrowCellId : CellId := 3
/-- The job payment: 30 of `payAsset`. -/
abbrev payAmt : Int := 30
/-- The delivery-condition witness frozen into the escrow cell. -/
abbrev deliveryCond : Int := 99

/-! ## §2 — Each market op as a GATED LEAF NODE through the production turn entry `execFullForestG`. -/

/-- A gated market node: credential `cred`, an action, no children — the production-entry shape. -/
def cxNode (cred : Authorization Dg Pf) (action : FullActionA) : DForest :=
  ⟨ mkAuth cred [], action, [] ⟩

/-- **order (mint leg)** — mint the factory escrow cell (`createCellFromFactoryA actor escrowCell vk`):
the cell is born carrying the escrow state machine + deal-term immutables. -/
def orderMintNode (cred : Authorization Dg Pf) (actor escrowCell : CellId) (vk : Int) : DForest :=
  cxNode cred (.createCellFromFactoryA actor escrowCell vk)

/-- **order (fund leg)** — fund the minted escrow cell: move `amount` of `asset` from the buyer into
the escrow cell's `bal` column (`balanceA`, the deposit move). -/
def orderFundNode (cred : Authorization Dg Pf) (buyerCell escrowCell : CellId) (asset : AssetId)
    (amount : Int) : DForest :=
  cxNode cred (.balanceA { actor := buyerCell, src := buyerCell, dst := escrowCell, amt := amount } asset)

/-! ## §3 — The leaf-collapse bridge: a childless gated forest runs EXACTLY its single gated node. -/

/-- **`execFullForestG_leaf` (the load-bearing collapse).** -/
theorem execFullForestG_leaf (s : RecChainedState) (na : DNodeAuth) (a : FullActionA) :
    execFullForestG s (⟨na, a, []⟩ : DForest) = execFullAGated s na a := by
  show (match execFullAGated s na a with
        | some s' => execFullChildrenG (targetOf a) s' ([] : List DChild)
        | none    => none) = execFullAGated s na a
  cases execFullAGated s na a with
  | none   => rfl
  | some _ => rfl

/-- **`execFullForestG_cxNode` — the market-op collapse.** A childless market op runs
`if gateOK then execFullA action else none`. -/
theorem execFullForestG_cxNode (s : RecChainedState) (cred : Authorization Dg Pf) (action : FullActionA) :
    execFullForestG s (cxNode cred action)
      = (if gateOK (mkAuth cred []) s = true then execFullA s action else none) := by
  rw [cxNode, execFullForestG_leaf, execFullAGated]

/-! ## §4 — The CREDENTIAL gate teeth (preserved verbatim across the re-point). -/

/-- The forged credential's gate leg is FALSE — independent of state, so `gateOK = false`. -/
theorem gateOK_forged_false (s : RecChainedState) : gateOK (mkAuth forgedCred []) s = false := by
  have hcred : credentialValidG (mkAuth forgedCred []) = false := by decide
  unfold gateOK
  rw [hcred]
  simp

/-- **`cx_forged_rejected` (gate teeth #1, preserved).** A market op (order-mint / order-fund /
ANY action) with a FORGED credential is rejected by the production turn entry, for EVERY pre-state. -/
theorem cx_forged_rejected (s : RecChainedState) (action : FullActionA) :
    execFullForestG s (cxNode forgedCred action) = none := by
  rw [cxNode]
  exact execFullForestG_unauthorized_fails s (mkAuth forgedCred []) action [] (gateOK_forged_false s)

/-- A FORGED order-mint is rejected (no minting an escrow cell without a credential). -/
theorem cx_forged_order_mint_rejected (s : RecChainedState) (actor escrowCell : CellId) (vk : Int) :
    execFullForestG s (orderMintNode forgedCred actor escrowCell vk) = none :=
  cx_forged_rejected s (.createCellFromFactoryA actor escrowCell vk)

/-- A FORGED order-fund is rejected (no funding without a credential). -/
theorem cx_forged_order_fund_rejected (s : RecChainedState) (buyerCell escrowCell : CellId)
    (asset : AssetId) (amount : Int) :
    execFullForestG s (orderFundNode forgedCred buyerCell escrowCell asset amount) = none :=
  cx_forged_rejected s
    (.balanceA { actor := buyerCell, src := buyerCell, dst := escrowCell, amt := amount } asset)

/-! ## §5 — The REVOCATION gate teeth (preserved verbatim). -/

/-- A gated market node carrying an explicit revocation NULLIFIER `nul`. -/
def cxNodeRevoked (cred : Authorization Dg Pf) (nul : Nat) (action : FullActionA) : DForest :=
  ⟨ { mkAuth cred [] with credNul := nul }, action, [] ⟩

/-- **`cx_revoked_rejected` (gate teeth #2, preserved).** A market op whose credential
nullifier `nul` is in the COMMITTED revocation registry is REJECTED, for EVERY pre-state and ANY
action — even with a genuine signature. Revocation reads committed state. -/
theorem cx_revoked_rejected (s : RecChainedState) (cred : Authorization Dg Pf) (nul : Nat)
    (action : FullActionA) (hrev : s.kernel.revoked.contains nul = true) :
    execFullForestG s (cxNodeRevoked cred nul action) = none := by
  rw [cxNodeRevoked]
  exact execFullForestG_unauthorized_fails s { mkAuth cred [] with credNul := nul } action []
    (gateOK_revoked_fails { mkAuth cred [] with credNul := nul } s hrev)

/-! ## §6 — The SETTLE-SAFETY CONTRACT, re-proved on the FACTORY-BORN cell.

These are the guarantees the verb-era `cx_*_conserves` / `cx_settle_requires_live_provider` carried,
now re-pointed onto the factory shape via the `EscrowFactory` keystones (which inherit the kernel
per-asset move law). The job's escrow cell `e` holds the payment in its OWN `bal` column;
`settle`/`refund` are the probe's `escrowRelease`/`escrowRefund`. -/

/-- **settle** — the provider is PAID (release the factory escrow `e` to `beneficiary`, gated on the
delivery-condition `witness`). -/
def settle (k : RecordKernelState) (e beneficiary : CellId) (asset : AssetId) (witness : Int) :
    Option RecordKernelState :=
  EscrowFactory.releaseEscrow k e beneficiary asset witness

/-- **refund** — the buyer is made WHOLE (refund the factory escrow `e` to `depositor`). -/
def refund (k : RecordKernelState) (e depositor : CellId) (asset : AssetId) :
    Option RecordKernelState :=
  EscrowFactory.refundEscrow k e depositor asset

/-- **`cx_order_mint_conserves` — THEOREM 3 (re-pointed).** Minting the factory escrow cell is
conservation-neutral for every asset (born EMPTY; the payment is funded separately). -/
theorem cx_order_mint_conserves {s s' : RecChainedState} {actor escrowCell : CellId} {vk : Int}
    (b : AssetId) (h : mintEscrowCell s actor escrowCell vk = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b :=
  mintEscrowCell_neutral b h

/-- **`cx_order_fund_conserves` — THEOREM 4 (re-pointed).** Funding the escrow cell (the payment move)
conserves every asset — the payment leaves the buyer's column and enters the escrow cell's column. -/
theorem cx_order_fund_conserves {k k' : RecordKernelState} {buyerCell escrowCell : CellId}
    {asset : AssetId} {amount : Int}
    (h : depositEscrow k buyerCell escrowCell asset amount = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b :=
  depositEscrow_conserves h b

/-- **`cx_settle_conserves` — THEOREM 5 (re-pointed).** A committed settle (release) conserves every
asset: the payment is DELIVERED from the held `bal` column, not conjured. -/
theorem cx_settle_conserves {k k' : RecordKernelState} {e beneficiary : CellId} {asset : AssetId}
    {witness : Int} (h : settle k e beneficiary asset witness = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b :=
  EscrowFactory.release_conserves h b

/-- **`cx_refund_conserves` — THEOREM 6 (re-pointed).** A committed refund conserves every asset. -/
theorem cx_refund_conserves {k k' : RecordKernelState} {e depositor : CellId} {asset : AssetId}
    (h : refund k e depositor asset = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b :=
  EscrowFactory.refund_conserves h b

/-- **`cx_no_double_resolve` — THEOREM 7 (factory shape).** Once a job has been settled (driven to
RELEASED), neither a second settle nor a refund commits — the installed state machine fail-closes.
The payment leaves the held column AT MOST ONCE. -/
theorem cx_no_double_resolve {k : RecordKernelState} {e tgt : CellId} {asset : AssetId} {witness : Int}
    (hres : escrowState k e = sReleased) :
    settle k e tgt asset witness = none ∧ refund k e tgt asset = none :=
  EscrowFactory.no_double_resolve hres

/-- **`cx_settle_requires_condition` — THEOREM 8 (release-only-on-condition).** A settle whose supplied
delivery witness ≠ the job's frozen `condition` slot is REJECTED — nobody collects without
demonstrating delivery. -/
theorem cx_settle_requires_condition {k : RecordKernelState} {e beneficiary : CellId} {asset : AssetId}
    {witness : Int} (hbad : witness ≠ escrowCondition k e) :
    settle k e beneficiary asset witness = none :=
  EscrowFactory.release_requires_condition hbad

/-- **`cx_settle_requires_live_provider` — THEOREM 9 (the D3 liveness teeth, factory shape).** A settle
whose provider is NOT a live account is REJECTED — the payment cannot be moved into a non-account
(which would silently destroy it). -/
theorem cx_settle_requires_live_provider {k : RecordKernelState} {e providerCell : CellId}
    {asset : AssetId} {witness : Int} (hdead : providerCell ∉ k.accounts) :
    settle k e providerCell asset witness = none :=
  EscrowFactory.release_requires_live_beneficiary hdead

/-- **`cx_refund_requires_live_buyer` — THEOREM 10 (the symmetric refund teeth).** A refund whose buyer
(refund target) is NOT a live account is REJECTED. -/
theorem cx_refund_requires_live_buyer {k : RecordKernelState} {e buyerCell : CellId} {asset : AssetId}
    (hdead : buyerCell ∉ k.accounts) :
    refund k e buyerCell asset = none :=
  EscrowFactory.refund_requires_live_depositor hdead

/-- **`cx_open_settleable` — THEOREM 11 (value-not-stranded, settle side).** A funded OPEN job with the
correct delivery condition and a `SettleReady` provider SETTLES (commits). -/
theorem cx_open_settleable {k : RecordKernelState} {e providerCell : CellId} {asset : AssetId}
    {witness : Int} (hopen : escrowState k e = sOpen) (hcond : witness = escrowCondition k e)
    (hr : SettleReady k e providerCell asset) :
    (settle k e providerCell asset witness).isSome :=
  EscrowFactory.open_releasable hopen hcond hr

/-- **`cx_open_refundable` — THEOREM 11 (value-not-stranded, refund side).** A funded OPEN job with a
`SettleReady` buyer REFUNDS (commits) — the abort path always returns the payment. -/
theorem cx_open_refundable {k : RecordKernelState} {e buyerCell : CellId} {asset : AssetId}
    (hopen : escrowState k e = sOpen) (hr : SettleReady k e buyerCell asset) :
    (refund k e buyerCell asset).isSome :=
  EscrowFactory.open_refundable hopen hr

/-! ## §7 — NON-VACUITY: a concrete FACTORY-BORN compute market, end to end + `#guard` witnesses.

`mkt0` is a funded market: the buyer (cell 0) holds 100 of the payment asset + a node-cap to the fresh
escrow cell `3`; the provider (cell 1) is a LIVE account holding 0. The escrow factory (payment 30,
depositor=buyer, beneficiary=provider, condition 99, asset 0) is published at key 7. We ORDER (mint
cell `3` from the factory, then fund it with 30), then witness the whole lifecycle on the factory-born
cell. -/

/-- A funded compute market: buyer holds 100 of `payAsset` + a node-cap to the escrow cell; provider is
a LIVE account holding 0. Publishes the escrow factory at key 7. Empty revocation registry. -/
def mkt0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun _ => .record [("balance", .int 0)]
        caps := fun c => if c = 0 then [Cap.node 3] else []
        bal := fun c a => if c = 0 ∧ a = 0 then 100 else 0
        factories := escrowRegistry 7 payAmt buyer provider deliveryCond payAsset }
    log := [] }

/-- ORDER: mint the factory escrow cell `3`, then fund it with 30 of the payment asset (buyer = cell 0),
each a gated op through `execFullForestG`. -/
def mktOrdered : Option RecChainedState :=
  (execFullForestG mkt0 (orderMintNode goodCred buyer escrowCellId cxVk)).bind
    (fun s => execFullForestG s (orderFundNode goodCred buyer escrowCellId payAsset payAmt))

-- the gate passes for the genuine credential, fails for the forged one:
#guard (gateOK (mkAuth goodCred []) mkt0)                       --  true
#guard (gateOK (mkAuth forgedCred []) mkt0) == false           --  false

-- (i) the ORDER mints + funds: the escrow cell `3` holds the locked 30 in ITS bal column:
#guard (mktOrdered.isSome)                                                                --  true (ordered!)
#guard (mktOrdered.map (fun s => s.kernel.bal escrowCellId payAsset)) == some 30           --  escrow holds 30
#guard (mktOrdered.map (fun s => s.kernel.bal buyer payAsset)) == some 70                  --  buyer 100→70
#guard (mktOrdered.map (fun s => escrowState s.kernel escrowCellId)) == some sOpen         --  OPEN
#guard (mktOrdered.map (fun s => escrowCondition s.kernel escrowCellId)) == some 99        --  condition installed
-- ...and the per-asset supply is FIXED (pure per-asset move conservation, NO side-table):
#guard (mktOrdered.map (fun s => recTotalAsset s.kernel payAsset)) == some 100             --  conserved

-- (ii) a FORGED order-mint ⇒ none (gate teeth):
#guard ((execFullForestG mkt0 (orderMintNode forgedCred buyer escrowCellId cxVk)).isSome) == false

-- (iii) a REVOKED order ⇒ none: a market whose registry holds nullifier 7, ordering with it rejects:
/-- A market whose revocation registry contains nullifier 7 (a revoked credential serial). -/
def mktRevoked : RecChainedState :=
  { kernel := { mkt0.kernel with revoked := [7] }, log := [] }
#guard (mktRevoked.kernel.revoked.contains 7)                                              --  true
#guard ((execFullForestG mktRevoked
          (cxNodeRevoked goodCred 7 (.createCellFromFactoryA buyer escrowCellId cxVk))).isSome) == false
-- ...and the SAME mint with a non-revoked nullifier (0) COMMITS (revocation is the sole reason above):
#guard ((execFullForestG mktRevoked
          (cxNodeRevoked goodCred 0 (.createCellFromFactoryA buyer escrowCellId cxVk))).isSome)  --  true

-- (iv) SETTLE (release with the delivery condition) pays the provider 30 (0→30), advances to RELEASED:
#guard (mktOrdered.bind (fun s => settle s.kernel escrowCellId provider payAsset deliveryCond)
        |>.map (fun k => k.bal provider payAsset)) == some 30
#guard (mktOrdered.bind (fun s => settle s.kernel escrowCellId provider payAsset deliveryCond)
        |>.map (fun k => k.bal escrowCellId payAsset)) == some 0
#guard (mktOrdered.bind (fun s => settle s.kernel escrowCellId provider payAsset deliveryCond)
        |>.map (fun k => escrowState k escrowCellId)) == some sReleased
#guard (mktOrdered.bind (fun s => settle s.kernel escrowCellId provider payAsset deliveryCond)
        |>.map (fun k => recTotalAsset k payAsset)) == some 100

-- (v) a WRONG delivery witness (7 ≠ 99) ⇒ none (release-only-on-condition):
#guard (mktOrdered.bind (fun s => settle s.kernel escrowCellId provider payAsset 7) |>.isSome) == false

-- (vi) REFUND returns the payment to the buyer (70→100) and advances to REFUNDED:
#guard (mktOrdered.bind (fun s => refund s.kernel escrowCellId buyer payAsset)
        |>.map (fun k => k.bal buyer payAsset)) == some 100
#guard (mktOrdered.bind (fun s => refund s.kernel escrowCellId buyer payAsset)
        |>.map (fun k => escrowState k escrowCellId)) == some sRefunded

-- (vii) NO-DOUBLE-RESOLVE: settle then a second settle AND a refund both fail:
#guard (mktOrdered.bind (fun s => settle s.kernel escrowCellId provider payAsset deliveryCond)
        |>.bind (fun k => settle k escrowCellId provider payAsset deliveryCond) |>.isSome) == false
#guard (mktOrdered.bind (fun s => settle s.kernel escrowCellId provider payAsset deliveryCond)
        |>.bind (fun k => refund k escrowCellId buyer payAsset) |>.isSome) == false

-- (viii) D3 LIVENESS TEETH: a settle into a NON-ACCOUNT provider (9) ⇒ none:
#guard (mktOrdered.bind (fun s => settle s.kernel escrowCellId 9 payAsset deliveryCond) |>.isSome) == false

/-! ## §8b — Hatchery bridge: production crowns on `trajG` (app semantics, not just per-op teeth). -/

/-- Per-baseline payment conservation contract (the compute market's `conservation% payAsset` shape). -/
noncomputable def cxPayConserved (s0 : RecChainedState) : Contract :=
  assetConserved s0 payAsset

/-- **`cx_pay_conserved_forever` — APP SEMANTICS (production crown).** From any baseline `s0`, along
EVERY adversarial production schedule, the payment asset's supply never drifts — the value-moving
market inherits the Hatchery `conservation%` shape on `trajG`. -/
theorem cx_pay_conserved_forever (s0 : RecChainedState) (sched : SchedG) :
    ∀ n, cellObsA (trajG s0 sched n) payAsset = cellObsA s0 payAsset :=
  asset_conserved_forever_production s0 payAsset sched

/-- The funded market's pay-asset observable is `100` (v4.35: stated once, so simp never unfolds
`mkt0` inside a trajectory). -/
private theorem cx_mkt0_pay_obs : cellObsA mkt0 payAsset = 100 := by
  simp [mkt0, payAsset, cellObsA, recTotalAsset]

/-- **`cx_mkt0_pay_conserved_forever` — the canonical funded-market production witness.** -/
theorem cx_mkt0_pay_conserved_forever (sched : SchedG) :
    ∀ n, cellObsA (trajG mkt0 sched n) payAsset = 100 :=
  fun n =>
    (cx_pay_conserved_forever mkt0 sched n).trans cx_mkt0_pay_obs

/-- **`cx_revoked_rejected_forever` — APP SEMANTICS (revocation crown).** If nullifier `nul` is in the
committed revocation registry initially, EVERY market op with that credential is rejected at EVERY
index of EVERY production schedule — composed from `gateRevoked` persistence + `cx_revoked_rejected`. -/
theorem cx_revoked_rejected_forever (s : RecChainedState) (cred : Authorization Dg Pf) (nul : Nat)
    (action : FullActionA) (hinit : nul ∈ s.kernel.revoked) (sched : SchedG) :
    ∀ n, execFullForestG (trajG s sched n) (cxNodeRevoked cred nul action) = none := by
  intro n
  exact cx_revoked_rejected (trajG s sched n) cred nul action
    (List.contains_iff_mem.mpr ((gateRevoked nul).forever hinit sched n))

/-- **`cx_revoked_pay_safety_forever` — COMPOSED APP CROWN (Identity ∩ ComputeExchange).** Revoked
nullifier stays in the committed registry AND the market payment asset's supply stays at the `mkt0`
baseline — one `revokedPaySafety` composed contract from `Verify/Contract.lean`. -/
theorem cx_revoked_pay_safety_forever (credNul : Nat) (s : RecChainedState)
    (hrev : credNul ∈ s.kernel.revoked)
    (hpay : cellObsA s payAsset = cellObsA mkt0 payAsset) (sched : SchedG) :
    ∀ n, credNul ∈ (trajG s sched n).kernel.revoked ∧
         cellObsA (trajG s sched n) payAsset = cellObsA mkt0 payAsset :=
  revoked_pay_safety_forever credNul mkt0 payAsset s hrev hpay sched

/-- **`cx_mkt0_revoked_pay_safety_forever` — funded-market composed witness (`s = mkt0`).** -/
theorem cx_mkt0_revoked_pay_safety_forever (credNul : Nat)
    (hrev : credNul ∈ mkt0.kernel.revoked) (sched : SchedG) :
    ∀ n, credNul ∈ (trajG mkt0 sched n).kernel.revoked ∧
         cellObsA (trajG mkt0 sched n) payAsset = 100 :=
  fun n => by
    have h := cx_revoked_pay_safety_forever credNul mkt0 hrev rfl sched n
    exact ⟨h.1, h.2.trans cx_mkt0_pay_obs⟩

/-! ## §10 — Axiom-hygiene tripwires (the honesty pins). Every keystone depends ONLY on the three
standard kernel axioms `{propext, Classical.choice, Quot.sound}`. -/

#assert_axioms execFullForestG_leaf
#assert_axioms execFullForestG_cxNode
#assert_axioms gateOK_forged_false
#assert_axioms cx_forged_rejected
#assert_axioms cx_revoked_rejected
#assert_axioms cx_order_mint_conserves
#assert_axioms cx_order_fund_conserves
#assert_axioms cx_settle_conserves
#assert_axioms cx_refund_conserves
#assert_axioms cx_no_double_resolve
#assert_axioms cx_settle_requires_condition
#assert_axioms cx_settle_requires_live_provider
#assert_axioms cx_refund_requires_live_buyer
#assert_axioms cx_open_settleable
#assert_axioms cx_open_refundable
#assert_axioms cx_pay_conserved_forever
#assert_axioms cx_mkt0_pay_conserved_forever
#assert_axioms cx_revoked_rejected_forever
#assert_axioms cx_revoked_pay_safety_forever
#assert_axioms cx_mkt0_revoked_pay_safety_forever

end Dregg2.Apps.ComputeExchangeGated

/-
# Market.CrossChainSettlement — DrEX RUNG 8: the ACCEPT-PATH MODEL of cross-chain settlement.

**What is on this page: a fair DrEX fill's settled root is a valid input to the settlement
verifier's accept-path — proved against an IN-FILE MODEL of that accept-path (`settleDrex`), over an
ABSTRACT root type. No statement below mentions a deployed contract, a foreign chain, or a Groth16
pairing.** The design this models (`docs/deos/DREX-DESIGN.md §4 rung 8, §3 #8`,
`docs/deos/INTERCHAIN-MODEL.md`): a proven DrEX clearing produces a settled state root, and a target
chain's verifier — the LIVE EVM `DreggSettlement.sol`, the DEMONSTRATED CosmWasm
`cosmos-settlement/`, the DEMONSTRATED Solana `solana-settlement/` (alt_bn128) — checks that root and
advances its own `provenRoot` to include the DrEX fill; no bridge validators, no wrapped tokens, no
custody. Those verifiers EXIST, but their correspondence to `settleDrex` is trust-by-reading (the
HONEST GRADE below names both scope edges). The clearing itself is a machine-checked, proof-carrying
executor turn (rungs 1–7); this rung composes that with a MODEL of the outbound settlement leg.

## The model (the clearing → root → settle chain)

A DrEX fill settles cross-chain when three things line up:

  (a) **the clearing is PROVEN** — a fair (`CycleValid`), conserving DrEX ring that SETTLES through
      the verified kernel executor (`settleRing pre (settlementsOf nodes) = some post`). This is
      rungs 1–7, KERNEL-REAL via `Market/LedgerRealizationExt.lean` (a cleared ring IS a
      `settleRing → recKExec` turn; its partial-fill lowering conserves on the real ledger,
      `partialFill_cycle_ledger_realized`). We bundle exactly this as `DrexClearing` — the
      proof-carrying fill the Groth16 settlement proof attests.

  (b) **the resulting state root is PROVEN to the target chain** — the settlement contract verifies a
      Groth16 proof of the dregg state transition `genesis_root → final_root` over `num_turns`
      (`DreggSettlement.sol::settle` step 4, the pairing check; the CosmWasm/Solana twins reproduce
      the SAME BN254 checks). The transition the proof attests is the DrEX clearing's `pre → post`:
      `final_root` IS `rootOf post`.

  (c) **the target chain ADVANCES its `provenRoot`** to include the DrEX fill — fail-closed on
      continuity (`genesisRoot == provenLanes`, the contract's `ContinuityBroken` check;
      `bridge/src/ethereum.rs::submit_eth_settlement`). We model this as `settleDrex`, the on-chain
      twin of `DreggSettlement.settle`'s accept-path.

## What is PROVED here (the composition) vs the honest scope

  * `drex_fill_cross_chain_settleable` (THE KEYSTONE) — a proven DrEX fill (`DrexClearing`: fair +
    conserving + kernel-real) whose pre-state root chains from the register's current proven root IS
    accepted by `settleDrex`, THE ACCEPT-PATH MODEL: it advances the register's `provenRoot` to the
    fill's post-state root (`rootOf post`) and its `provenHeight` by the batch's turn count — while
    the fill it settles is simultaneously the rung-1 conserving + fair clearing on the REAL executor
    ledger. The clearing → root → settle chain is one theorem AT THAT RESOLUTION: "settle-able"
    means, exactly, accepted by this file's model of the verifier's accept-path.

  * FAIL-CLOSED, both teeth:
      - `settleDrex_continuity_broken` — a fill that does NOT chain from the current proven root is
        REFUSED (the `ContinuityBroken` gate — a fill cannot be replayed onto a foreign anchor);
      - `unfair_clearing_not_settleable` / `wrongAsset_clearing_not_settleable` — an over-debiting or
        wrong-asset "clearing" produces NO `DrexClearing` witness at all (it is not `CycleValid`,
        `Market.overdebit_refused` / `wrongAsset_refused`), so there is nothing to settle;
      - `no_minting_drex_clearing` / `minting_post_unsettleable` — a value-MINTING post-state is
        UNREACHABLE by `settleRing` (`settleRing_conserves`), so the verifier can NEVER advance its
        proven root to a value-minting root. A non-conserving/unfair clearing does not produce a
        settle-able root.

  * NON-VACUITY, both polarities: a concrete proven DrEX fill (`demoFill` — the `validSwapCycle`
    bilateral swap settling through a real kernel state with sufficient balances) settles cross-chain
    and genuinely ADVANCES the proven root (`demo_fill_settles_cross_chain`, `demo_root_advances`);
    and the same fill against a mismatched anchor is REFUSED (`demo_fill_refused_wrong_root`).

**HONEST GRADE — the clearing → root → settle chain is PROVED at SPEC level; the verifiers EXIST
(EVM LIVE, Cosmos/Solana demonstrated).** Two scope edges, named not hidden:

  * The **settlement verifier is modelled as its accept-path** (`settleDrex`: the continuity gate +
    the proven-root advance), the on-chain twin of `DreggSettlement.settle`. The Groth16 PAIRING
    check (`verifier.verifyProof`) — that a proof `π` attests the transition `pre → post` — is the
    circuit obligation `DrexClearing.settled`/`.valid` STAND IN for: here the transition is a genuine
    conserving executor turn by construction. The pairing itself is the crypto floor the deployed
    verifier already checks (Groth16 over BN254; `chain/gnark/`), on a single-party **dev ceremony**
    setup (toxic-waste-known), not mainnet MPC — the rung-8 caveat `DREX-DESIGN.md §6` names once.

  * The **DrEX → settlement PROOF-GENERATION wiring** — turning a real DrEX fill into a FRESH Groth16
    settlement proof whose `final_root` is `rootOf post` — is the NAMED build. At HEAD it is blocked
    on the fixture-geometry bug a sibling is fixing; the VERIFIERS that check such a proof already
    EXIST and one (`DreggSettlement.sol`) is LIVE on Base-Sepolia (`chain/DEPLOYMENTS.md`). This
    module proves the SPEC the proof-gen must realize: that a fair DrEX clearing's settled root IS a
    valid input to the settlement verifier's accept-path.

Cross-chain ATOMICITY of a *single multilateral cycle whose legs settle on different chains* (a
commit/abort protocol across verifiers) is a further open rung (`DREX-DESIGN.md §6`, RESEARCH); this
module settles a whole DrEX fill's root onto ONE target chain — the outbound leg, the buildable-now
capstone.

Pure. No new axioms — every bridge composes existing kernel + clearing keystones.
-/
import Market.LedgerRealizationExt
import Dregg2.Tactics

namespace Market

open Dregg2.Intent.Ring
open Dregg2.Exec (AssetId CellId RecordKernelState recTotalAsset Value)

set_option autoImplicit false

/-! ## 1. THE TARGET-CHAIN SETTLEMENT STATE — the `provenRoot`/`provenHeight` register. -/

/-- **`ProvenState Root`** — the target chain's settlement register: the state-machine `DreggSettlement`
maintains (`_provenLanes`/`_provenHeight`; the CosmWasm/Solana twins advance the SAME two fields). A
cross-chain verifier gates message acceptance on `isProvenRoot`, i.e. on the history of `provenRoot`
values this register has advanced through. `Root` is the target chain's root representation (EVM: the
`packLanes` keccak of the 8 BabyBear state lanes). -/
structure ProvenState (Root : Type) where
  /-- The dregg state root the target chain has proven up to (`provenRoot()`). -/
  provenRoot   : Root
  /-- The cumulative number of dregg turns proven (`provenHeight()`, strictly growing). -/
  provenHeight : Nat
deriving Repr

/-! ## 2. A PROVEN DrEX FILL — the bundle the settlement proof attests. -/

/-- **`DrexClearing`** — a PROVEN DrEX fill: a fair (`CycleValid`), conserving clearing that SETTLES
through the verified kernel executor. This is exactly rungs 1–7 KERNEL-REAL (`settleRing → recKExec`,
the proven turn `Market/LedgerRealizationExt.lean` welds): the matched cycle `nodes` clears fairly
(`valid` + `wantPos`) and its ledger settlement commits (`settled`). The Groth16 settlement proof
attests THIS state transition `pre → post`; the fields are precisely what a faithful proof-gen must
witness (the transition is a genuine conserving executor turn). -/
structure DrexClearing where
  /-- The pre-clearing kernel state (the `genesis_root` side of the settlement proof). -/
  pre     : RecordKernelState
  /-- The post-clearing kernel state (the `final_root` side). -/
  post    : RecordKernelState
  /-- The matched cycle the solver cleared. -/
  nodes   : List MatchNode
  /-- FAIR — the cycle is graph-admitted (`CycleValid`; over-debiting/wrong-asset cycles are refused). -/
  valid   : CycleValid nodes
  /-- Positive declared minimums (the ring balances; `cycleValid_settlement_balanced` needs it). -/
  wantPos : ∀ n ∈ nodes, 0 < n.wantMin
  /-- KERNEL-REAL — the clearing SETTLES through the verified executor (rung-1's `settleRing` tie). -/
  settled : settleRing pre (settlementsOf nodes) = some post

/-- A `DrexClearing`'s batch settles a non-empty ring — a `CycleValid` cycle has ≥ 2 legs, so the
settlement contract's `numTurns > 0` (`ZeroTurns`) check is ALWAYS satisfied by a real DrEX fill. -/
theorem DrexClearing.numTurns_pos (c : DrexClearing) : 0 < c.nodes.length := by
  have := c.valid.len; omega

/-! ## 3. THE SETTLEMENT VERIFIER'S ACCEPT-PATH — the on-chain twin of `DreggSettlement.settle`. -/

/-- **`settleDrex rootOf S c`** — the target chain's settlement verifier applied to a DrEX fill `c`
(the on-chain twin of `DreggSettlement.sol::settle`, and its CosmWasm/Solana peers). It advances the
proven-root register to the fill's post-state root iff the fill CHAINS from the current proven root:

  * **continuity** (`rootOf c.pre = S.provenRoot`) — the settlement's `genesis_root` must equal the
    current `provenRoot` (the contract's `ContinuityBroken` gate, `DreggSettlement.sol:210-215`;
    `bridge/src/ethereum.rs`'s `advance.old_root != state.proven_root` rejection). FAIL-CLOSED: a fill
    that does not chain from the current anchor is REFUSED (`none`) — it cannot be replayed onto a
    foreign root.

On accept, `provenRoot` advances to `rootOf c.post` (the proof's `final_root`) and `provenHeight`
grows by the batch's turn count (`_provenHeight += numTurns`). The Groth16 pairing check
(`verifier.verifyProof`, step 4) is what proves `c.pre → c.post` is a genuine transition; here that is
`c.settled`/`c.valid` by construction. `numTurns > 0` is automatic (`DrexClearing.numTurns_pos`). -/
def settleDrex {Root : Type} [DecidableEq Root] (rootOf : RecordKernelState → Root)
    (S : ProvenState Root) (c : DrexClearing) : Option (ProvenState Root) :=
  if rootOf c.pre = S.provenRoot then
    some { provenRoot := rootOf c.post, provenHeight := S.provenHeight + c.nodes.length }
  else
    none

/-! ## 4. THE KEYSTONE — a fair DrEX fill is accepted by the settlement accept-path model. -/

/-- **`drex_fill_cross_chain_settleable` — DrEX RUNG 8, the settlement composition, in the accept-path
MODEL.** Read the name at its real resolution: "cross-chain settleable" means ACCEPTED BY `settleDrex`
— this file's model of the verifier's accept-path, over an abstract `rootOf` — and nothing in the
statement reaches a deployed verifier or another chain (HONEST GRADE, header). A PROVEN DrEX fill `c`
(`DrexClearing`: fair `CycleValid`, conserving, KERNEL-REAL via `settleRing`) whose pre-state root
chains from the register's current proven root (`hcont`) is accepted:

  * **(SETTLE)** `settleDrex` advances the modeled proven-root register: its new `provenRoot` is the
    DrEX fill's post-state root `rootOf c.post` (the settlement proof's `final_root`), and its
    `provenHeight` grows by the batch's turn count.
  * **(CONSERVING, kernel-real)** the settled transition preserves every asset's supply on the REAL
    executor ledger (`settleRing_conserves` — the fill mints/burns nothing);
  * **(FAIR)** the settlement is structurally `RingBalanced` (no phantom value) AND every leg respects
    its declared limits — debited only its offered asset ≤ its offer, credited its wanted asset ≥ its
    minimum (`clearing_respects_limits`);
  * **(PRICED, kernel-real)** the priced partial-fill lowering conserves over ℚ
    (`pricedPartialFills_conserves`) — the settled root is the SAME trades as the rung-5 priced
    clearing, the model↔kernel correspondence `Market/LedgerRealizationExt.lean` welds.

The clearing → root → settle chain, as one theorem: a fair DrEX clearing's settled root IS a valid
input to the accept-path model (fail-closed — see §5). What a DEPLOYED verifier inherits from this is
conditional on the two named scope edges in the header. -/
theorem drex_fill_cross_chain_settleable {Root : Type} [DecidableEq Root]
    (rootOf : RecordKernelState → Root) (S : ProvenState Root) (c : DrexClearing)
    (hcont : rootOf c.pre = S.provenRoot) :
    ∃ S' : ProvenState Root,
      settleDrex rootOf S c = some S'
      ∧ S'.provenRoot = rootOf c.post
      ∧ S'.provenHeight = S.provenHeight + c.nodes.length
      ∧ (∀ b : AssetId, recTotalAsset c.post b = recTotalAsset c.pre b)
      ∧ RingBalanced (settlementsOf c.nodes)
      ∧ (∀ j, j < c.nodes.length →
          ((chainedLeg (c.nodes.map MatchNode.toRingNode) j).asset
              = (c.nodes.getD j default).offerAsset ∧
            (chainedLeg (c.nodes.map MatchNode.toRingNode) j).amount
              ≤ (c.nodes.getD j default).offerAmount) ∧
          (receivedAsset c.nodes j = (c.nodes.getD j default).wantAsset ∧
            (c.nodes.getD j default).wantMin ≤ receivedAmount c.nodes j))
      ∧ Conserves (pricedPartialFills c.nodes) := by
  refine ⟨{ provenRoot := rootOf c.post, provenHeight := S.provenHeight + c.nodes.length }, ?_,
    rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rw [settleDrex, if_pos hcont]
  · exact settleRing_conserves (settlementsOf c.nodes) c.pre c.post c.settled
  · exact cycleValid_settlement_balanced c.valid c.wantPos
  · intro j hj
    exact ⟨(settlement_from_sender_within_offer c.valid j hj).2,
           cycle_individuallyRational c.valid j hj⟩
  · exact pricedPartialFills_conserves c.valid c.wantPos

/-- **The proven-root advance, projected** — after settling a DrEX fill that chains from the current
proven root, the target chain's `provenRoot` IS the fill's post-state root. This is what makes the
fill queryable via `isProvenRoot(finalRoot)` on the target chain (`DreggSettlement.sol:227`,
`_provenRoots[packLanes(finalRoot)] = true`): a cross-chain verifier can now check any message against
the DrEX fill's settled root. -/
theorem drex_fill_advances_proven_root {Root : Type} [DecidableEq Root]
    (rootOf : RecordKernelState → Root) (S : ProvenState Root) (c : DrexClearing)
    (hcont : rootOf c.pre = S.provenRoot) :
    ∃ S' : ProvenState Root, settleDrex rootOf S c = some S' ∧ S'.provenRoot = rootOf c.post := by
  obtain ⟨S', hset, hroot, _⟩ := drex_fill_cross_chain_settleable rootOf S c hcont
  exact ⟨S', hset, hroot⟩

/-! ## 5. FAIL-CLOSED — a non-conserving / unfair / mis-anchored fill is REFUSED. -/

/-- **TOOTH (continuity): a fill that does not chain from the proven root is REFUSED.** If the fill's
pre-state root is not the target chain's current `provenRoot`, `settleDrex` fails-closed (`none`) —
the `ContinuityBroken` gate. A DrEX fill cannot be replayed onto a foreign anchor: it settles only as
the continuation of the exact state the chain has already proven. -/
theorem settleDrex_continuity_broken {Root : Type} [DecidableEq Root]
    (rootOf : RecordKernelState → Root) (S : ProvenState Root) (c : DrexClearing)
    (hbreak : rootOf c.pre ≠ S.provenRoot) :
    settleDrex rootOf S c = none := by
  rw [settleDrex, if_neg hbreak]

/-- **TOOTH (unfair give-side): an over-debiting clearing produces NO settle-able fill.** Ring.lean's
`underfundCycle` (node 1 demands 50 against node 0's offer of 3) is not `CycleValid`
(`Market.overdebit_refused`), so it cannot be packaged as a `DrexClearing` at all — there is no
proof-carrying fill for the verifier to settle. Fairness is enforced at FORMATION, upstream of the
settlement proof: an unfair clearing has no settle-able root. -/
theorem unfair_clearing_not_settleable : ¬ ∃ c : DrexClearing, c.nodes = underfundCycle := by
  rintro ⟨c, hc⟩
  exact overdebit_refused (hc ▸ c.valid)

/-- **TOOTH (unfair receive-side): a wrong-asset clearing produces NO settle-able fill.** Ring.lean's
`assetMismatchCycle` (node 1 wants asset 99 against node 0's offer of asset 10) is not `CycleValid`
(`Market.wrongAsset_refused`), so no `DrexClearing` carries it — a clearing that would credit an
un-wanted asset has no settle-able root. -/
theorem wrongAsset_clearing_not_settleable : ¬ ∃ c : DrexClearing, c.nodes = assetMismatchCycle := by
  rintro ⟨c, hc⟩
  exact wrongAsset_refused (hc ▸ c.valid)

/-- **TOOTH (conservation): a value-MINTING post-state is UNREACHABLE by settlement.** If a candidate
post-state `k''` mints (or burns) any asset relative to the pre-state `k` (`recTotalAsset k'' b ≠
recTotalAsset k b`), then `settleRing` CANNOT produce it (`settleRing_conserves`). So no minting
transition can be a `DrexClearing.settled` output, and the verifier can NEVER advance its proven root
to a value-minting root — a non-conserving clearing does not settle. -/
theorem minting_post_unsettleable (k k'' : RecordKernelState) (ns : List MatchNode) (b : AssetId)
    (hmint : recTotalAsset k'' b ≠ recTotalAsset k b) :
    settleRing k (settlementsOf ns) ≠ some k'' := by
  intro h
  exact hmint (settleRing_conserves (settlementsOf ns) k k'' h b)

/-- **The conservation guarantee on every settle-able fill** — a `DrexClearing`'s post-state conserves
every asset against its pre-state (`settleRing_conserves`). So the DrEX fill the verifier settles has
already preserved supply on the real ledger, before any root is advanced: the settled root only ever
commits a conserving transition. -/
theorem no_minting_drex_clearing (c : DrexClearing) (b : AssetId) :
    recTotalAsset c.post b = recTotalAsset c.pre b :=
  settleRing_conserves (settlementsOf c.nodes) c.pre c.post c.settled b

/-! ## 6. NON-VACUITY, POSITIVE POLE — a concrete proven DrEX fill settles cross-chain. -/

/-- A concrete pre-clearing kernel state where `validSwapCycle` settles: cells 1 and 2 are live
accounts holding exactly the assets the swap moves — cell 1 holds 7 of asset 10 (its leg sends
`wantMin[1] = 7`), cell 2 holds 5 of asset 11 (its leg sends `wantMin[0] = 5`). Every other balance is
0. Authorization is self-send (`actor = from_` in every chained leg), so the executor gate passes. -/
def demoSettlePre : RecordKernelState where
  accounts := {1, 2}
  cell := fun c =>
    if c ∈ ({1, 2} : Finset CellId) then Value.record [("balance", Value.int 0)] else default
  caps := fun _ => []
  bal := fun c a => if c = 1 ∧ a = 10 then 7 else if c = 2 ∧ a = 11 then 5 else 0

/-- The post-clearing kernel state — the swap settled through the verified executor. -/
def demoSettlePost : RecordKernelState :=
  (settleRing demoSettlePre (settlementsOf validSwapCycle)).get (by decide)

/-- The concrete swap SETTLES through the verified kernel — both legs commit (cell 1 → 2 of 7 asset 10,
cell 2 → 1 of 5 asset 11), all-or-nothing. -/
theorem demoSettle_settles :
    settleRing demoSettlePre (settlementsOf validSwapCycle) = some demoSettlePost :=
  (Option.some_get (by decide)).symm

/-- **A concrete PROVEN DrEX fill** — the `validSwapCycle` bilateral swap, fair + kernel-real. -/
def demoFill : DrexClearing where
  pre     := demoSettlePre
  post    := demoSettlePost
  nodes   := validSwapCycle
  valid   := validSwapCycle_valid
  wantPos := by decide
  settled := demoSettle_settles

/-- A demonstrative state root that distinguishes the demo states — a genuine (state-dependent)
projection of the ledger. (The deployed root is the Poseidon2/keccak `recStateCommit` packing of the
8 BabyBear lanes; ANY faithful state-distinguishing root exhibits the continuity gate biting. Here the
pre/post are separated by the balances the swap moved.) -/
def demoRoot (k : RecordKernelState) : ℤ × ℤ := (k.bal 1 10, k.bal 2 11)

/-- The target chain's register, anchored at the DrEX fill's pre-state root. -/
def demoProven : ProvenState (ℤ × ℤ) := { provenRoot := (7, 5), provenHeight := 0 }

/-- **TRUE POLE — the concrete DrEX fill SETTLES CROSS-CHAIN.** Its pre-state root chains from the
target chain's proven anchor, so the verifier accepts: it advances the proven root to the fill's
post-state root and grows the proven height by the 2-leg batch. A genuine private-of-nothing,
fair, conserving DrEX fill is settle-able on the target chain. -/
theorem demo_fill_settles_cross_chain :
    ∃ S' : ProvenState (ℤ × ℤ),
      settleDrex demoRoot demoProven demoFill = some S'
      ∧ S'.provenRoot = demoRoot demoFill.post
      ∧ S'.provenHeight = 2 := by
  obtain ⟨S', hset, hroot, hheight, _⟩ :=
    drex_fill_cross_chain_settleable demoRoot demoProven demoFill (by decide)
  exact ⟨S', hset, hroot, hheight.trans (by decide)⟩

/-- **The proven root genuinely ADVANCES** — the DrEX fill's post-state root `(0, 0)` (both cells'
holdings moved) is DIFFERENT from the pre-anchor `(7, 5)`. So settling the fill is a real state change
on the target chain, not a no-op: the register moves to include the DrEX fill. -/
theorem demo_root_advances : demoRoot demoFill.post ≠ demoProven.provenRoot := by decide

/-! ## 7. NON-VACUITY, NEGATIVE POLE — the teeth bite on the concrete fill. -/

/-- The register anchored at a FOREIGN root the DrEX fill does not continue. -/
def demoProvenBad : ProvenState (ℤ × ℤ) := { provenRoot := (99, 99), provenHeight := 0 }

/-- **FALSE POLE — the same DrEX fill against a MISMATCHED anchor is REFUSED.** The fill's pre-state
root `(7, 5)` does not equal the foreign proven root `(99, 99)`, so `settleDrex` fails-closed
(`ContinuityBroken`). The verifier settles the fill only as the continuation of the exact state the
chain has already proven — a fill cannot be replayed onto a foreign anchor. -/
theorem demo_fill_refused_wrong_root : settleDrex demoRoot demoProvenBad demoFill = none := by
  apply settleDrex_continuity_broken
  decide

/-- **The discriminator, assembled** (the laundering guard): the SAME DrEX fill settles from the
matching anchor and is REFUSED from a foreign one. The cross-chain settlement is not a `True`-carrier:
continuity genuinely gates it. -/
theorem demo_cross_chain_discriminates :
    (∃ S' : ProvenState (ℤ × ℤ), settleDrex demoRoot demoProven demoFill = some S')
    ∧ settleDrex demoRoot demoProvenBad demoFill = none :=
  ⟨(drex_fill_advances_proven_root demoRoot demoProven demoFill (by decide)).imp
      (fun _ h => h.1),
   demo_fill_refused_wrong_root⟩

/-- The concrete fill's roots, COMPUTED and NAMED: the pre-anchor root is `(7, 5)` (cell 1 holds 7 of
asset 10, cell 2 holds 5 of asset 11) and the settled post root is `(0, 0)` (both holdings moved —
the swap cleared). (Retired `#guard`s, named; the other four guards were closed instances of
`demo_root_advances`, `demo_fill_settles_cross_chain`, `demo_fill_refused_wrong_root`, and the
2-leg length already pinned by `demo_fill_settles_cross_chain`'s `provenHeight = 2`, and are
subsumed by those named theorems.) -/
theorem demo_roots_computed :
    (demoRoot demoSettlePre, demoRoot demoSettlePost) = (((7 : ℤ), (5 : ℤ)), ((0 : ℤ), (0 : ℤ))) := by
  decide

/-! ## Axiom hygiene — every cross-chain-settlement keystone pinned kernel-clean (CI hard-gate). -/

#assert_all_clean [Market.DrexClearing.numTurns_pos, Market.drex_fill_cross_chain_settleable,
  Market.drex_fill_advances_proven_root, Market.settleDrex_continuity_broken,
  Market.unfair_clearing_not_settleable, Market.wrongAsset_clearing_not_settleable,
  Market.minting_post_unsettleable, Market.no_minting_drex_clearing, Market.demoSettle_settles,
  Market.demo_fill_settles_cross_chain, Market.demo_root_advances, Market.demo_roots_computed,
  Market.demo_fill_refused_wrong_root, Market.demo_cross_chain_discriminates]

end Market

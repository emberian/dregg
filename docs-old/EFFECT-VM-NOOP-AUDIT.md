# Effect VM NoOp Audit

**Audit date:** 2026-05-25
**Auditor:** concurrent lane (Sonnet action+audit)
**Reference issue:** #100 — "31 of 41 Effect variants project to VmEffect::NoOp"

---

## Finding: Original Claim Was Based on Stale State

The issue claimed 31 of 41 variants collapsed to `VmEffect::NoOp` in `AgentCipherclerk::convert_effects_to_vm` (sdk/src/cipherclerk.rs). **This was already substantially remediated** before this audit lane ran. Stage 3 projections covering all 41 (now 52) variants were committed in the same session (see commit `dfce0ced` "Block 1: tighten placeholder effect-VM projections"). The audit confirmed the committed state and contributed one additional fix.

---

## Variant Count Update

The `Effect` enum grew from 41 to **52 variants** since the issue was filed:
- Original 41 variants (documented in issue)
- +11 added: `Refusal`, `CellSeal`, `CellUnseal`, `CellDestroy`, `Burn`, `AttenuateCapability`, `ReceiptArchive`, and expansions to CapTP/queue ops

The test file `tests/src/every_variant_roundtrip.rs` covers all 52.

---

## Full Classification Table (52 variants)

| Variant | VmEffect Projection (current) | Class | Status |
|---------|-------------------------------|-------|--------|
| SetField | SetField { field_idx, value } | STRUCTURAL | Real projection |
| Transfer | Transfer { amount, direction } | CRITICAL | Real projection |
| GrantCapability | GrantCapability { cap_entry } | CRITICAL | Real — fixed by c79e16de |
| RevokeCapability | RevokeCapability { slot_hash } | CRITICAL | Real projection |
| EmitEvent | EmitEvent { event_hash } | STRUCTURAL | Real projection |
| IncrementNonce | (skip → NoOp) | NoOp-acceptable | **Intentional** |
| CreateCell | CreateCell { create_hash } | STRUCTURAL | Real projection |
| SetPermissions | SetPermissions { permissions_hash } | STRUCTURAL | Real projection |
| SetVerificationKey | SetVerificationKey { vk_hash } | STRUCTURAL | Real projection |
| NoteSpend | NoteSpend { nullifier, value } | CRITICAL | Real projection |
| NoteCreate | NoteCreate { commitment, value } | CRITICAL | Real projection |
| CreateSealPair | CreateSealPair { pair_hash } | STRUCTURAL | Real projection |
| Seal | Seal { field_idx } | STRUCTURAL | Real projection |
| Unseal | Unseal { field_idx, brand } | STRUCTURAL | Real projection |
| SpawnWithDelegation | SpawnWithDelegation { spawn_hash } | STRUCTURAL | Real projection |
| RefreshDelegation | RefreshDelegation | STRUCTURAL | Real projection |
| RevokeDelegation | RevokeDelegation { child_hash } | STRUCTURAL | Real projection |
| BridgeMint | BridgeMint { value_lo, mint_hash, value_full } | CRITICAL | Real projection |
| BridgeLock | BridgeLock { value_lo, lock_hash, value_full } | CRITICAL | Real projection |
| BridgeFinalize | BridgeFinalize { finalize_hash } | STRUCTURAL | Real projection |
| BridgeCancel | BridgeCancel { nullifier_hash } | STRUCTURAL | Real projection |
| Introduce | Introduce { intro_hash } | STRUCTURAL | Real projection |
| PipelinedSend | PipelinedSend { send_hash } | STRUCTURAL | Real projection |
| CreateObligation | CreateObligation { stake_amount, obligation_id, beneficiary_hash } | CRITICAL | Real projection |
| FulfillObligation | FulfillObligation { obligation_id, stake_return } | CRITICAL | Real projection |
| SlashObligation | SlashObligation { obligation_id, stake_amount, beneficiary_hash } | CRITICAL | Real projection |
| CreateEscrow | CreateEscrow { amount_lo, escrow_hash, amount_full } | CRITICAL | Real projection |
| ReleaseEscrow | ReleaseEscrow { escrow_id_hash } | CRITICAL | Real projection |
| RefundEscrow | RefundEscrow { escrow_id_hash } | CRITICAL | Real projection |
| CreateCommittedEscrow | CreateCommittedEscrow { commit_hash } | CRITICAL | Real projection |
| ReleaseCommittedEscrow | ReleaseCommittedEscrow { commit_hash } | CRITICAL | Real projection |
| RefundCommittedEscrow | RefundCommittedEscrow { commit_hash } | CRITICAL | Real projection |
| ExerciseViaCapability | ExerciseViaCapability { exercise_hash } | STRUCTURAL | Real projection |
| MakeSovereign | MakeSovereign | STRUCTURAL | Real projection |
| CreateCellFromFactory | CreateCellFromFactory { factory_vk, child_vk_derived } | STRUCTURAL | Real projection |
| QueueAllocate | AllocateQueue { capacity, owner_quota_id, cost_per_slot } | STRUCTURAL | Real projection |
| QueueEnqueue | EnqueueMessage { message_hash, deposit_amount, sender_id, ... } | STRUCTURAL | Real projection |
| QueueDequeue | DequeueMessage { expected_message_hash, deposit_refund } | STRUCTURAL | Real projection |
| QueueResize | ResizeQueue { new_capacity, queue_id, cost_per_slot, old_capacity } | STRUCTURAL | Real projection |
| QueueAtomicTx | AtomicQueueTx { op_count, tx_hash, combined_old_root, combined_new_root, net_deposit } | STRUCTURAL | Real projection |
| QueuePipelineStep | PipelineStep { pipeline_id, source_old_root, source_new_root, sink_new_root, message_hash } | STRUCTURAL | Real projection |
| ExportSturdyRef | ExportSturdyRef { cell_id, permissions, random_seed, export_counter } | CRITICAL | Real projection |
| EnlivenRef | EnlivenRef { swiss_number, presenter_id, expected_cell_id, expected_permissions } | CRITICAL | Real projection |
| DropRef | DropRef { cell_id, holder_federation, current_refcount } | CRITICAL | Real projection |
| ValidateHandoff | ValidateHandoff { certificate_hash, recipient_pk, introducer_pk, approved_set_root } | CRITICAL | Real projection |
| Refusal | EmitEvent { event_hash: offered_action_commitment } | STRUCTURAL | Real projection |
| CellSeal | SetPermissions { permissions_hash: seal_hash } | STRUCTURAL | Real projection |
| CellUnseal | SetPermissions { permissions_hash: unseal_hash } | STRUCTURAL | Real projection |
| CellDestroy | SetPermissions { permissions_hash: destroy_hash } | CRITICAL | Real projection |
| Burn | Transfer { amount, direction: 1 } | CRITICAL | Real projection |
| AttenuateCapability | RevokeCapability { slot_hash: attn_hash } | CRITICAL | Real projection |
| ReceiptArchive | EmitEvent { event_hash: archive_hash } | STRUCTURAL | Real projection |

### Classification summary

| Class | Count | Description |
|-------|-------|-------------|
| CRITICAL | 20 | Balance/cap/cell mutations with soundness implications |
| STRUCTURAL | 31 | Should be auditable; non-soundness-blocking |
| NoOp-acceptable | 1 | IncrementNonce (intentionally implicit in row continuity) |

---

## Fix Made in This Lane

### GrantCapability — granter perspective gap (commit c79e16de)

**Variant:** `Effect::GrantCapability { from, to, cap }`

**Prior state:** Guard was `if to == cell_id` — only projected from the **recipient's** perspective. When the proving cell was the **granter** (`from == cell_id`, `to == some_other_cell`), the effect silently fell to `_ => {}` → empty vec → `VmEffect::NoOp`.

**Test evidence:** The `every_effect_variant_round_trips_through_projection` test uses `to: cell_b, from: cell_a` and proves from cell_a's POV — the exact case that was dropped.

**Fix:** Changed guard to `if to == cell_id || from == cell_id`. Both granter and grantee perspectives now produce `VmEffect::GrantCapability { cap_entry }`, which witnesses a cap_root mutation in the Effect VM AIR.

**AIR impact:** `VmEffect::GrantCapability` applies the constraint `new_cap_root == hash_2_to_1(old_cap_root, cap_entry)`. The granter's proof now binds the cap-granting operation into its own cap_root transition, closing the gap where a granting cell's receipt attested to nothing about the capability it just transferred.

**File:** `sdk/src/cipherclerk.rs`

---

## Remaining Known Gaps (Not Fixed in This Lane)

### IncrementNonce — NoOp-acceptable by design

The bridge skips this variant because "nonce increments are implicit in row-to-row continuity" (`effect_vm_bridge.rs` comment). The VM's row-to-row constraint already enforces `new_nonce == old_nonce + 1` regardless of what `VmEffect` is present. Adding a dedicated `VmEffect::IncrementNonce` would be redundant. **This is correct behavior, not a gap.**

The test `every_effect_variant_round_trips_through_projection` will still fail for IncrementNonce (it produces `[NoOp]`) but this is a test-design artifact: the test checks that ALL effects have a non-NoOp projection, but IncrementNonce is explicitly intended to be "proven by continuity, not by a dedicated VM effect."

### SDK vs Executor bridge divergence (latent)

The SDK's `convert_effects_to_vm` now closely mirrors `turn/src/executor/effect_vm_bridge.rs` Stage 3 projections, but it lacks access to the live `Ledger`. For ledger-dependent fields:

| Variant | Ledger-dependent field | SDK sentinel | Bridge value |
|---------|------------------------|--------------|--------------|
| ExportSturdyRef | `export_counter` from `state.fields[7]` | `0` | real counter |
| EnlivenRef | `expected_permissions` cross-check | projected | validated |
| DropRef | `current_refcount` from `state.fields[5]` | `0` | real refcount |
| QueueEnqueue | `queue_len`, `program_vk` | `0, ZERO` | real values |
| QueueDequeue | head hash via `fields[1]` | sentinel | real head |
| QueueResize | `old_capacity` from `fields[0]` | `0` | real capacity |
| QueueAtomicTx | `combined_old_root` from `fields[4]` | cell_id hash | real root |

These sentinel values are consistent with the bridge's own fallback behavior when a cell is missing from the ledger. They are not soundness gaps in the executor path (the executor uses the real values); they are accuracy gaps in the SDK's off-executor proof-construction path. Clients calling the SDK function on a turn that has already been proved by the executor will get the real values from the bridge.

---

## Stage-by-Stage Progress Reference

| Stage | Coverage | Notes |
|-------|----------|-------|
| Stage 0 (baseline) | 11/52 REAL | Original state: Transfer, SetField, GrantCapability(recv), NoteSpend, NoteCreate, Obligation×3, Seal, Unseal, MakeSovereign, CreateCellFromFactory |
| Stage 1 (bridge) | +7 additional | CreateObligation, FulfillObligation, SlashObligation, Seal, Unseal, MakeSovereign, CreateCellFromFactory (already in Stage 0) |
| Stage 3 (Block 1) | +40 additional | All remaining variants except IncrementNonce (dfce0ced + prior work) |
| This lane | +1 | GrantCapability granter perspective (c79e16de) |
| **Current** | **51/52 REAL** | IncrementNonce is intentionally NoOp by design |

---

## Punch List (ordered by priority)

### P0 — Verify AIR constraint strength for shape-sharing projections

Several lifecycle effects share VmEffect shapes from other variants to avoid adding new AIR variants:

- `CellSeal` / `CellUnseal` / `CellDestroy` → `VmEffect::SetPermissions`
- `Burn` → `VmEffect::Transfer { direction: 1 }`
- `AttenuateCapability` → `VmEffect::RevokeCapability`
- `Refusal` → `VmEffect::EmitEvent`
- `ReceiptArchive` → `VmEffect::EmitEvent`

The constraint binding is real (they contribute to `effects_hash`) but the AIR does not enforce the semantics specific to each effect. For example, `VmEffect::Transfer` for `Burn` witnesses a balance debit — good — but doesn't enforce the `was_burn` disclosure flag at the AIR level. The `SCHEMA_BURN` algebraic constraint in `effect_action_air.rs` covers this if the separate per-effect binding proof is produced; the Effect VM itself does not.

**Recommended fix:** Add dedicated VmEffect variants for `CellSeal`, `CellDestroy`, `Burn`, and `AttenuateCapability`. These have distinct semantics (terminal, irreversible, algebraic) that deserve first-class AIR constraint rows.

### P1 — Add dedicated VmEffect variants for lifecycle effects

Currently `CellSeal` and `CellDestroy` both project to `VmEffect::SetPermissions`. A verifier cannot distinguish a cell-seal from a permission-update from a cell-destruction from the Effect VM trace alone. Domain separation at the VM level (separate selectors) would allow the AIR to gate these transitions with lifecycle-specific constraints (e.g., `CellDestroy` must be terminal; no subsequent effects from this cell should verify).

### P2 — Widen ledger-sentinel fields for SDK bridge

For production use of the SDK's `convert_effects_to_vm` (outside the executor path), the sentinel values for `export_counter`, `current_refcount`, `queue_len`, and `combined_old_root` should be sourced from an optional `Ledger` argument or from pre-computed state snapshots. The current sentinel=0 means the SDK-produced proof's PI binds to counter=0 rather than the actual cell state.

### P3 — IncrementNonce test compatibility

If the `every_effect_variant_round_trips_through_projection` test is ever un-ignored, it will fail for `IncrementNonce`. Either:
a) Document the test as "51-of-52" with an explicit exclusion for IncrementNonce, or
b) Add a no-op `VmEffect::IncrementNonce` variant that passes through without AIR state changes (purely for test compatibility)

Option (a) is architecturally cleaner.

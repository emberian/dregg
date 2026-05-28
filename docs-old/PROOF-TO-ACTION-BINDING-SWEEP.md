# PROOF-TO-ACTION-BINDING-SWEEP — per-Effect audit of proof-to-action binding

**Date:** 2026-05-24. **Status:** in-flight (implementation lane). **Scope:**
every variant of `turn::action::Effect`, with attention to whether the
executor's projection into `dregg_circuit::effect_vm::Effect` and the AIR's
public inputs together provide *algebraic*, *full-fidelity* binding of the
action parameters.

This document is the per-Effect counterpart to `CAVEAT-LAYER-COVERAGE.md`
§4. The goal of this lane is to apply the discipline established by the
just-landed `bridge_action_air` / `bridge::action_binding` pair — every
32-byte field carried by a runtime `Effect` is bound as 8 × 4-byte BabyBear
limbs (~248-bit binding strength), every `u64` amount as 2 × 32-bit limbs
(full 64-bit binding) — to *every* runtime `Effect` variant.

The bridge AIR pattern (`circuit/src/bridge_action_air.rs`) is the
benchmark: each PI slot is *exactly* a trace-row-0 boundary constraint on
a column carrying one limb. Tampering on any byte of any field changes
the limb encoding, which mismatches the boundary, which fails STARK
verification.

---

## §0 — Methodology

For each `Effect` variant we record:

- **Action parameters** — the typed fields the runtime variant carries.
- **Binding verdict** — for each parameter:
  - ✅ **bound**: full-fidelity, no truncation, no aliasing, no
    placeholder.
  - ⚠ **partial**: hashed-then-truncated (e.g., 4-byte BabyBear), or
    bound as a domain-tagged hash rather than the raw bytes, or one
    parameter is bound but a sibling is not.
  - ✗ **unbound**: a placeholder (ZERO / 1 / alias of another field)
    sits in the AIR PI; the AIR's constraint is tautologically
    satisfied with no algebraic link to the actual parameter.
- **Current AIR column / PI slot** — citing
  `circuit/src/effect_vm.rs:LLLL` for the variant-specific row.
- **Owner lane** — `this-lane` (proof-to-action binding sweep) vs
  `substrate-AIR` (the in-flight lane closing 9 named placeholder
  variants) vs `closed` (already at full fidelity).

The 30-bit truncation regression on u64 amounts has already been closed
by the `value_full` / `amount_full` field additions on
`{BridgeMint, BridgeLock, CreateEscrow}`
(`circuit/src/effect_vm.rs:1000-1033`); those rows are marked **closed**
below.

---

## §1 — Per-Effect table

Legend on Owner lane:
- **closed** — already full-fidelity.
- **substrate** — owned by the substrate-AIR lane (do NOT double-fix).
- **this-lane** — owned by this proof-to-action binding sweep.
- **structural** — passthrough with no domain-specific binding to do.

| # | Effect (runtime) | Parameters | Current AIR PI | Verdict | Owner |
|---|---|---|---|---|---|
| 1 | `SetField { cell, index, value: [u8;32] }` | `index: u32`, `value: 32B` | `VmEffect::SetField { field_idx: u32, value: BabyBear }` — `value` is `field_element_to_bb([0..4])` (executor.rs:2562) | ⚠ value 4-byte truncated; index full | **this-lane** |
| 2 | `Transfer { from, to, amount: u64 }` | `amount: u64`, direction bit | `VmEffect::Transfer { amount: u64, direction: u32 }` — full u64 (effect_vm.rs:931) | ✅ | **closed** |
| 3 | `GrantCapability { from, to, cap }` | `cap.slot: u32`, `cap.target, cap.permissions, cap.allowed_effects` | `VmEffect::GrantCapability { cap_entry: BabyBear }` — `hash_to_bb(blake3(slot.to_le_bytes()))` (executor.rs:2566) — binds ONLY the slot number, not target/permissions/allowed_effects | ✗ target/permissions/allowed_effects unbound; slot 4-byte truncated | **this-lane** |
| 4 | `RevokeCapability { cell, slot: u32 }` | `slot: u32` | `VmEffect::RevokeCapability { slot_hash: BabyBear }` — `hash_to_bb(blake3(slot.to_le_bytes()))` (executor.rs:2876) — slot bound modulo 4-byte hash collision | ⚠ 4-byte hash truncation | **this-lane** |
| 5 | `EmitEvent { cell, event }` | `event.topic: Symbol`, `event.data: Vec<FieldElement>` | `VmEffect::EmitEvent { event_hash: BabyBear }` — 4-byte truncation of BLAKE3(topic ‖ data) (executor.rs:2920) | ⚠ 4-byte hash truncation; full Event opaque | **this-lane** |
| 6 | `IncrementNonce { cell }` | none | (implicit row-to-row continuity, no projection) | ✅ | **closed** |
| 7 | `CreateCell { public_key, token_id, balance }` | `public_key: 32B`, `token_id: 32B`, `balance: u64` | `VmEffect::CreateCell { create_hash: BabyBear }` — 4-byte truncation of BLAKE3(pk ‖ tok ‖ bal) (executor.rs:2893) | ⚠ 4-byte hash truncation; component fields not split-out | **this-lane** |
| 8 | `SetPermissions { cell, new_permissions }` | `new_permissions: Permissions` | `VmEffect::SetPermissions { permissions_hash: BabyBear }` — 4-byte truncation of BLAKE3(postcard(perm)) (executor.rs:2853) | ⚠ 4-byte hash truncation | **this-lane** |
| 9 | `SetVerificationKey { cell, new_vk }` | `new_vk: Option<VerificationKey>` | `VmEffect::SetVerificationKey { vk_hash }` — 4-byte truncation; None→0 (executor.rs:2868) | ⚠ 4-byte hash truncation | **this-lane** |
| 10 | `NoteSpend { nullifier, note_tree_root, value, asset_type, spending_proof, value_commitment }` | `nullifier: 32B`, `note_tree_root: 32B`, `value: u64`, `asset_type: u64`, `value_commitment: Option<32B>` | `VmEffect::NoteSpend { nullifier: BabyBear, value: u64 }` (effect_vm.rs:1050) — nullifier 4-byte truncated; tree_root / asset_type / value_commitment **not in PI** | ✗ note_tree_root unbound; asset_type unbound; value_commitment unbound; nullifier 4-byte truncated | **this-lane** (high impact: replay protection narrowly intact via tree_root verification path off-AIR) |
| 11 | `NoteCreate { commitment, value, asset_type, encrypted_note, value_commitment, range_proof }` | `commitment: 32B`, `value: u64`, `asset_type: u64`, `encrypted_note: Vec<u8>`, `value_commitment: Option<32B>`, `range_proof: Option<Vec<u8>>` | `VmEffect::NoteCreate { commitment: BabyBear, value: u64 }` (effect_vm.rs:1052) — commitment 4-byte truncated; asset_type/value_commitment/range_proof_hash unbound | ✗ asset_type unbound; value_commitment unbound; commitment 4-byte truncated | **this-lane** |
| 12 | `CreateSealPair { sealer_holder, unsealer_holder }` | two `CellId` (32B each) | `VmEffect::CreateSealPair { pair_hash: BabyBear }` — 4-byte truncation of BLAKE3(sealer ‖ unsealer) (executor.rs:2907) | ⚠ 4-byte hash truncation | **this-lane** |
| 13 | `Seal { pair_id: 32B, capability }` | `pair_id`, `capability` | `VmEffect::Seal { field_idx: u32 }` — `(pair_id[0] as u32) & 0x7` (executor.rs:2809); capability not bound; field_idx is fabricated from pair_id low bits | ✗ pair_id unbound; capability unbound | **substrate** |
| 14 | `Unseal { sealed_box, recipient }` | `sealed_box: SealedBox`, `recipient: CellId` | `VmEffect::Unseal { field_idx, brand }` — both fabricated (executor.rs:2818) | ✗ sealed_box unbound; recipient unbound | **substrate** |
| 15 | `SpawnWithDelegation { child_public_key, child_token_id, max_staleness }` | `child_pk: 32B`, `child_token_id: 32B`, `max_staleness: u64` | `VmEffect::SpawnWithDelegation { spawn_hash: BabyBear }` — 4-byte truncation (executor.rs:2938) | ⚠ 4-byte hash truncation; max_staleness folded into hash | **this-lane** |
| 16 | `RefreshDelegation` | none | `VmEffect::RefreshDelegation` (no params) | ✅ | **closed** |
| 17 | `RevokeDelegation { child }` | `child: CellId` (32B) | `VmEffect::RevokeDelegation { child_hash: BabyBear }` — 4-byte truncation (executor.rs:2950) | ⚠ 4-byte truncation | **this-lane** |
| 18 | `BridgeMint { portable_proof }` | `portable_proof: PortableNoteProof` with nullifier, source_root, dest_federation, asset_type, value | `VmEffect::BridgeMint { value_lo, mint_hash, value_full }` (effect_vm.rs:1028-1033) — value_full is u64; mint_hash is 4-byte truncation of BLAKE3(null ‖ root ‖ dest_fed ‖ asset_type) | ✅ via sibling `bridge_action_air` (8 limbs per 32B field + 2 limbs amount). The action-binding AIR is the canonical full-fidelity binding; the VmEffect 4-byte hash is dispatch-only. | **closed** (via bridge_action_air) |
| 19 | `BridgeLock { nullifier, destination, value, asset_type, timeout_height, spending_proof }` | nullifier 32B, destination 32B, value u64, asset_type u64, timeout_height u64 | `VmEffect::BridgeLock { value_lo, lock_hash, value_full }` (effect_vm.rs:1012-1017) | ⚠ destination not bound via 8-limb form; timeout_height not in PI; value_full present | **this-lane** (extend sibling AIR coverage to lock too) |
| 20 | `BridgeFinalize { nullifier, receipt }` | nullifier 32B, receipt: BridgeReceipt | `VmEffect::BridgeFinalize { finalize_hash: BabyBear }` — 4-byte (executor.rs:3016) | ⚠ 4-byte truncation | **this-lane** |
| 21 | `BridgeCancel { nullifier }` | nullifier 32B | `VmEffect::BridgeCancel { nullifier_hash: BabyBear }` — 4-byte (effect_vm.rs:979) | ⚠ 4-byte truncation | **this-lane** |
| 22 | `Introduce { introducer, recipient, target, permissions }` | introducer/recipient/target CellId (32B), permissions: AuthRequired | `VmEffect::Introduce { intro_hash }` — 4-byte truncation of BLAKE3(introducer ‖ recipient ‖ target ‖ perm_byte) (executor.rs:3056) | ✗ individual 32B cells collapsed into a single 4-byte digest | **this-lane** |
| 23 | `PipelinedSend { target, action }` | target: EventualRef (source_turn 32B + output_slot u32), action: Box<Action> | `VmEffect::PipelinedSend { send_hash }` — 4-byte truncation (executor.rs:3069) | ⚠ 4-byte hash truncation; action.hash() embedded inside | **this-lane** |
| 24 | `CreateObligation { beneficiary, condition, deadline_height, stake, stake_amount }` | beneficiary 32B, condition, deadline_height u64, stake: NoteCommitment (32B), stake_amount u64 | `VmEffect::CreateObligation { stake_amount: u64, obligation_id, beneficiary_hash }` — obligation_id and beneficiary 4-byte truncated; stake_amount u64 full; condition + deadline_height unbound (effect_vm.rs:1055) | ⚠ 4-byte stake/beneficiary; deadline_height unbound; condition unbound | **this-lane** |
| 25 | `FulfillObligation { obligation_id, proof }` | obligation_id 32B, proof: ConditionProof | `VmEffect::FulfillObligation { obligation_id, stake_return: u64 }` — `stake_return: 0` placeholder (executor.rs:2792) | ✗ stake_return placeholder; proof unbound | **substrate** |
| 26 | `SlashObligation { obligation_id }` | obligation_id 32B | `VmEffect::SlashObligation { obligation_id, stake_amount: u64, beneficiary_hash }` — `stake_amount: 0` placeholder (executor.rs:2798) | ✗ stake_amount placeholder | **substrate** |
| 27 | `CreateEscrow { cell, recipient, amount, condition, timeout_height, escrow_id }` | recipient 32B, amount u64, condition: EscrowCondition, timeout_height u64, escrow_id 32B | `VmEffect::CreateEscrow { amount_lo, escrow_hash, amount_full: u64 }` (effect_vm.rs:1000) — amount_full full; escrow_hash 4-byte truncation of BLAKE3(recipient ‖ condition); escrow_id NOT bound; timeout_height unbound | ⚠ escrow_id unbound; timeout_height unbound; recipient folded into 4-byte digest; amount_full ✅ | **this-lane** |
| 28 | `ReleaseEscrow { escrow_id, proof }` | escrow_id 32B, proof: Option<Vec<u8>> | `VmEffect::ReleaseEscrow { escrow_id_hash }` — 4-byte truncation (executor.rs:3102) | ⚠ 4-byte truncation; proof unbound | **this-lane** |
| 29 | `RefundEscrow { escrow_id }` | escrow_id 32B | `VmEffect::RefundEscrow { escrow_id_hash }` — 4-byte truncation (executor.rs:3108) | ⚠ 4-byte truncation | **this-lane** |
| 30 | `CreateCommittedEscrow { creator_commitment, recipient_commitment, value_commitment, condition_commitment, timeout_height, escrow_id, range_proof, amount }` | 5×32B commitments + range_proof + amount u64 | `VmEffect::CreateCommittedEscrow { commit_hash }` — 4-byte truncation of BLAKE3(creator ‖ recipient ‖ value ‖ condition); escrow_id/range_proof/amount unbound | ✗ amount unbound (privacy-preserving via Pedersen, but the *executor* still applies a balance change — the proof should bind to which balance change); escrow_id unbound; timeout_height unbound | **this-lane** |
| 31 | `ReleaseCommittedEscrow { escrow_id, claim_auth, recipient }` | escrow_id 32B, claim_auth, recipient 32B | `VmEffect::ReleaseCommittedEscrow { commit_hash }` — 4-byte truncation (executor.rs:3142) | ⚠ 4-byte truncation; claim_auth unbound | **this-lane** |
| 32 | `RefundCommittedEscrow { escrow_id, claim_auth, creator }` | escrow_id 32B, claim_auth, creator 32B | `VmEffect::RefundCommittedEscrow { commit_hash }` — 4-byte truncation (executor.rs:3154) | ⚠ 4-byte truncation; claim_auth unbound | **this-lane** |
| 33 | `ExerciseViaCapability { cap_slot, inner_effects }` | cap_slot u32, inner_effects: Vec<Effect> | `VmEffect::ExerciseViaCapability { exercise_hash }` — 4-byte truncation of BLAKE3(cap_slot ‖ inner_effects[*].hash()) (executor.rs:3172) | ⚠ 4-byte truncation; inner_effects.len() unbound; cap_slot folded into hash | **this-lane** |
| 34 | `MakeSovereign { cell }` | none beyond cell identity | `VmEffect::MakeSovereign` (no params; selector + state transition mode_flag 0→1) | ✅ | **closed** |
| 35 | `CreateCellFromFactory { factory_vk, owner_pubkey, token_id, params }` | factory_vk 32B, owner_pubkey 32B, token_id 32B, params | `VmEffect::CreateCellFromFactory { factory_vk: BabyBear, child_vk_derived: BabyBear }` — both 4-byte truncations (executor.rs:2831); params unbound | ⚠ 4-byte truncations; params unbound; token_id unbound | **this-lane** |
| 36 | `QueueAllocate { capacity, program_vk }` | capacity u64, program_vk Option<32B> | `VmEffect::AllocateQueue { capacity: u32, owner_quota_id, cost_per_slot: 1 }` (executor.rs:2595) | ⚠ capacity u64→u32 truncation; program_vk dropped entirely; cost_per_slot hardcoded | **substrate** |
| 37 | `QueueEnqueue { queue, message_hash, deposit }` | queue 32B, message_hash 32B, deposit u64 | `VmEffect::EnqueueMessage { ..., queue_len: 0, program_vk: ZERO }` (executor.rs:2624) | ✗ queue_len placeholder; program_vk placeholder; queue not bound explicitly (folded into sender_id) | **substrate** |
| 38 | `QueueDequeue { queue }` | queue 32B | `VmEffect::DequeueMessage { expected_message_hash: domain-tagged hash of queue, deposit_refund: 0 }` (executor.rs:2656) | ✗ expected_message_hash aliased to queue id; deposit_refund placeholder | **substrate** |
| 39 | `QueueResize { queue, new_capacity }` | queue 32B, new_capacity u64 | `VmEffect::ResizeQueue { new_capacity: u32, queue_id, cost_per_slot:1, old_capacity:0 }` (executor.rs:2674) | ✗ old_capacity placeholder | **substrate** |
| 40 | `QueueAtomicTx { operations }` | operations: Vec<QueueTxOp> | `VmEffect::AtomicQueueTx { op_count, tx_hash, combined_old_root, combined_new_root, net_deposit }` — combined_old_root cell_id-derived, transition uses Poseidon2 chain rather than self-loop (executor.rs:2728) | ⚠ combined_old_root not tied to actual ledger queue root; tx hash binds operations | **substrate** |
| 41 | `QueuePipelineStep { pipeline_id, source, sinks }` | pipeline_id 32B, source 32B, sinks: Vec<CellId> | `VmEffect::PipelineStep { pipeline_id, source_old_root, source_new_root, sink_new_root, message_hash }` — fabricated triangle (executor.rs:2753) | ✗ source_old_root fabricated; only first sink bound | **substrate** |
| 42 | `ExportSturdyRef { swiss_number, target }` | swiss_number 32B, target 32B | `VmEffect::ExportSturdyRef { cell_id, permissions:ZERO, random_seed, export_counter:0 }` (executor.rs:3229) | ✗ permissions placeholder; export_counter placeholder | **substrate** |
| 43 | `EnlivenRef { swiss_number, bearer }` | swiss_number 32B, bearer 32B | `VmEffect::EnlivenRef { swiss_number, presenter_id, expected_cell_id: domain-tagged, expected_permissions: ZERO }` (executor.rs:3268) | ✗ expected_permissions placeholder; expected_cell_id derived not from ledger | **substrate** |
| 44 | `DropRef { ref_id }` | ref_id 32B | `VmEffect::DropRef { cell_id, holder_federation, current_refcount:1 }` (executor.rs:3298) | ✗ current_refcount placeholder | **substrate** |
| 45 | `ValidateHandoff { cert_hash }` | cert_hash 32B | `VmEffect::ValidateHandoff { certificate_hash, recipient_pk: derived, introducer_pk: derived, approved_set_root: ZERO }` (executor.rs:3353) | ✗ recipient_pk/introducer_pk not from actual cert; approved_set_root via federation PI now | **substrate** |

**Tally (this lane's responsibility — 25 variants):**

- ✅ closed (full-fidelity): 5 (`Transfer`, `IncrementNonce`,
  `RefreshDelegation`, `MakeSovereign`, `BridgeMint` via sibling AIR).
- ⚠ partial (4-byte hash truncation; this lane will widen to 8-limb): 17.
- ✗ unbound parameters present: 3 (`GrantCapability`, `Introduce`,
  `CreateCommittedEscrow`).

**Substrate-AIR lane responsibility (12 variants):** `Seal`, `Unseal`,
`FulfillObligation`, `SlashObligation`, `QueueAllocate`,
`QueueEnqueue`, `QueueDequeue`, `QueueResize`, `QueueAtomicTx`,
`QueuePipelineStep`, `ExportSturdyRef`, `EnlivenRef`, `DropRef`,
`ValidateHandoff`.

---

## §2 — Approach: a generalized effect-action binding AIR

The bridge-action sibling AIR has a clean shape: each 32-byte field
becomes 8 BabyBear limbs (4 bytes each, `BabyBear::new(u32)`); each u64
becomes 2 BabyBear limbs (low + high 32 bits). Each limb is a PI slot,
pinned to a row-0 column via a boundary constraint. Transition
constraints force every row to equal row 0 (so a malicious prover
cannot put one set of bytes in row 0 and another set in row 1).

To avoid writing one AIR per effect variant, this lane introduces a
parameterized `effect_action_air` module
(`circuit/src/effect_action_air.rs`) that accepts:

- A *static* schema (list of named 32-byte fields + list of named u64
  amounts) per effect kind.
- A *witness* (the typed parameter values for one particular effect
  instance).

The schema is a `const &[FieldSpec]` per effect. The witness is the
effect's struct passed through `EffectActionWitness::from_xxx(...)`
helpers. The AIR generates the trace + PIs from the witness and the
boundary constraints from the PI vector and the schema.

This pattern matches `bridge_action_air` so closely that we could in
principle reformulate `bridge_action_air` on top of
`effect_action_air`; we don't, to preserve the existing standalone
proof shape that `bridge::action_binding::PortableActionBinding`
consumes. The generalized AIR is added alongside the specialized one.

---

## §3 — Cross-cutting items

### §3.1 — Multi-effect ordering

The Effect VM (`circuit/src/effect_vm.rs`) executes effects in trace
order: row N applies `VmEffect[N]`. The `effects_hash` accumulator
(`circuit/src/effect_vm.rs::effects_hash` column, near line 1500) is
order-sensitive: it chains `hash(effects_hash_prev, effect_payload)`,
so swapping two effects yields a different `effects_hash` and a
different turn-root.

**Verdict on ordering:** ✅ **bound** at the VM level by the row-order
hash chain. No explicit `ORDER_INDEX` column needed; the row index
itself is the order. A malicious prover cannot permute effects without
breaking the hash chain.

The bridge-action sibling AIR is order-irrelevant within itself (single
effect per AIR instance), so this concern is local to the Effect VM.

### §3.2 — Witness-blob → Effect indexing

The runtime `Action` carries `witness_blobs: Vec<WitnessBlob>` and the
cell-side evaluators reference blobs by `proof_witness_index` (see
`turn/src/action.rs:82-100` and `cell/src/preconditions.rs`). The
Effect VM currently does NOT bind which witness blob feeds which
effect: the runtime executor consumes blobs at evaluation time, but
the AIR has no per-effect-row `witness_blob_index` PI slot.

**Verdict on witness-blob indexing:** ✗ **unbound** at the AIR level.

**Closure plan:** add a `witness_blob_index: u32` column to the Effect
VM per row, pin it as PI per effect, and have the executor populate it
when constructing `VmEffect` from `Effect`. This is a low-cost
extension; the AIR doesn't need to *use* the index beyond pinning it
(consumption happens at the off-chain witness-resolver). Marker
TODO[witness-effect-binding] in `circuit/src/effect_vm.rs` near the
row-layout constants.

This is **deferred** in this lane (requires Effect VM column-width
expansion + coordinated landing with the executor's witness-resolution
plumbing).

### §3.3 — Cross-Effect within-turn chains

Example: `SpendNote(N)` followed by `BridgeMint` consuming `N`'s
nullifier. Today the AIR proves each effect's projection independently;
no in-AIR constraint says "the nullifier in row K's NoteSpend matches
the nullifier consumed in row K+M's BridgeMint".

**Verdict on cross-Effect chains:** ✗ **unbound** at the AIR level.
The executor enforces this via `BridgedNullifierSet` (see
`cell/src/note_bridge.rs::BridgedNullifierSet` and
`turn/src/executor.rs:6582+`), but the proof itself does not witness
the chain.

**Closure plan:** introduce a per-row `consumes_row: Option<u32>` PI
column. When `NoteSpend` is in row K and `BridgeMint` references its
nullifier, the executor populates `BridgeMint.row[consumes_row] = K`
and the AIR adds the boundary constraint `row[K].nullifier == row[K+M].consumed_nullifier`.

This is **deferred** in this lane (needs Effect VM row-layout
expansion; coordinated landing).

---

## §4 — Closures landed in this lane

The closures use a generalized `effect_action_air` AIR
(`circuit/src/effect_action_air.rs`) parameterized over a per-Effect
`EffectActionSchema` (`field_count`, `amount_count`, and `kind_name`
for Fiat-Shamir domain separation). Each closure consists of:

1. A `pub const SCHEMA_<EFFECT_NAME>` declaration with the per-effect
   list of 32-byte fields and u64 amounts.
2. Honest round-trip test (`prove_effect_action` →
   `verify_effect_action`).
3. Per-parameter tamper-reject tests (single byte flip on each field;
   ±1 on each amount).
4. Where applicable: positional-binding tests (swap two fields → reject),
   30-bit-truncation-rejected tests (high-bit amount must not collide
   with low-30-bit form), cross-kind proof-confusion test (kind A
   proof must not verify as kind B).

Closures landed (commit `ce79a735` + `20124ca3`):

- **§4.1** `GrantCapability` — binds `cap.target` (32B), permissions
  hash (32B), allowed_effects hash (32B), `cap.slot` (u64). 4 tamper
  tests + roundtrip.
- **§4.2** `RevokeCapability` — binds `cell_id` (32B) and `slot` (u64).
- **§4.3** `EmitEvent` — binds `topic` (32B), `data_hash` (32B),
  `data_len` (u64).
- **§4.4** `CreateCell` — binds `public_key` (32B), `token_id` (32B),
  `balance` (full u64). Includes regression test that a balance with
  bit 50 set is NOT verified as its low-30-bit truncation.
- **§4.5** `SetPermissions` — binds `cell_id` (32B), `permissions_hash`
  (32B).
- **§4.6** `SetVerificationKey` — binds `cell_id` (32B), `vk_hash`
  (32B; ZERO for None). Includes cross-kind confusion test against
  `SetPermissions` (same shape, different `kind_name`).
- **§4.7** `Introduce` — binds 3 × `CellId` (introducer, recipient,
  target) + `permissions_vk_hash` (32B; zero for non-Custom) +
  `permissions_discriminant` (u64). Includes a swap-recipient/target
  rejection test.
- **§4.8** `CreateSealPair` — binds `sealer_holder` (32B),
  `unsealer_holder` (32B). Includes a swap rejection test.
- **§4.9** `BridgeFinalize` — binds `nullifier` (32B), `receipt_hash`
  (32B).
- **§4.10** `BridgeCancel` — binds `nullifier` (32B).
- **§4.11** `RevokeDelegation` — binds `child` (32B).
- **§4.12** `SpawnWithDelegation` — binds `child_pk` (32B),
  `child_token_id` (32B), `max_staleness` (u64).
- **§4.13** `ReleaseEscrow` — binds `escrow_id` (32B), `proof_hash`
  (32B). Includes cross-kind separation test (a release proof must
  not verify as a refund proof).
- **§4.14** `RefundEscrow` — binds `escrow_id` (32B).
- **§4.15** `ExerciseViaCapability` — binds `inner_effects_hash` (32B),
  `cap_slot` (u64), `inner_effects_len` (u64). Length-binding closes
  the gap where a different-length inner-effect chain with a colliding
  hash prefix could project to the same VmEffect.
- **§4.16** `CreateObligation` — binds `beneficiary` (32B),
  `condition_hash` (32B), `stake_commitment` (32B), `deadline_height`
  (u64), `stake_amount` (u64). Includes 30-bit-truncation-rejected
  test for stake_amount.
- **§4.17** `CreateEscrow` — binds `recipient` (32B), `condition_hash`
  (32B), `escrow_id` (32B), `amount` (u64), `timeout_height` (u64).
  Closes the executor gap where `escrow_id` and `timeout_height` were
  dropped from VmEffect.
- **§4.18** `PipelinedSend` — binds `source_turn` (32B), `action_hash`
  (32B), `output_slot` (u64).
- **§4.19** `CreateCellFromFactory` — binds `factory_vk` (32B),
  `owner_pubkey` (32B), `token_id` (32B), `params_hash` (32B). Closes
  the executor gap where `token_id` and `params` were dropped.
- **§4.20** `CreateCommittedEscrow` — binds 6 commitment fields (32B
  each) + `amount` (cleartext u64) + `timeout_height` (u64). Closes
  the executor gap where the cleartext amount the executor balance-
  debits is not pinned in the proof (the Pedersen commitment + range
  proof hide the value from observers, but the proof-to-action
  binding must still pin what the executor will apply).

Total: **20 per-Effect closures**, each with adversarial tamper-reject
tests. The two source commits are:

  - `ce79a735` — generalized AIR + 8 schemas (GrantCapability through
    CreateSealPair).
  - `20124ca3` — 11 additional schemas (BridgeFinalize through
    CreateCommittedEscrow) + 12 additional tests.

The AIR is `circuit/src/effect_action_air.rs::EffectActionAir`. It is
a sidecar binding AIR (sibling to the Effect VM proof, not a
replacement) — the Effect VM proof retains its 4-byte hash truncations
for backwards compatibility of the existing trace shape; the sidecar
binding proof is what a verifier consults for algebraic, full-fidelity
parameter binding.

---

## §5 — Deferred items

- **§3.2** Witness-blob → Effect indexing (needs Effect VM column
  expansion).
- **§3.3** Cross-Effect within-turn chain pinning (needs Effect VM row
  layout expansion).
- **NoteSpend** — `note_tree_root`, `asset_type`, `value_commitment`
  binding expansion. Partially overlaps with the deprecated
  `note_spending_air`'s existing PIs; needs coordination with the
  note-spend AIR maintainer to avoid double-binding and to bind
  `asset_type` / `value_commitment` explicitly.
  Marker: `circuit/src/note_spending_air.rs` is deprecated; expand via
  the DSL or sibling.
- **NoteCreate** — `asset_type` and `value_commitment` binding (same
  rationale as NoteSpend).
- **Executor wire-in** — `convert_turn_effects_to_vm`
  (`turn/src/executor.rs:2511`) currently projects each runtime
  `Effect` to a `VmEffect` for the Effect-VM AIR. To make the new
  sidecar binding proofs available to verifiers, a follow-up commit
  will (a) attach a `Vec<EffectBindingProof>` field to the turn's
  on-wire shape, (b) populate one entry per effect using
  `prove_effect_action` with the appropriate schema, and (c) extend
  the verifier path to check every binding proof against the
  executor's view of the effect parameters.
- **BridgeLock sibling AIR** — analogous to `bridge_action_air` for
  mint, but for lock: binds `nullifier`, `destination`,
  `asset_type`, `value`, `timeout_height` at full fidelity. The
  existing `value_full` field on `VmEffect::BridgeLock` covers the
  30-bit gap on `value`, but `destination`, `timeout_height`, and
  `asset_type` remain unbound in the lock-side projection.
- **Substrate-AIR lane** — the 12 placeholder-bearing variants
  (`Seal`, `Unseal`, `Queue*`, CapTP-`*`, `FulfillObligation`,
  `SlashObligation`) are owned by that lane; once they're at full
  fidelity, the corresponding schemas can be added here as well.

---

## §6 — Files of record

- `circuit/src/bridge_action_air.rs` — the canonical pattern (662
  lines). Single-effect (bridge mint) binding AIR.
- `circuit/src/effect_action_air.rs` — new in this lane. Generalized
  effect-binding AIR that supports an arbitrary list of 32-byte fields
  and u64 amounts.
- `bridge/src/action_binding.rs` — the bridge-side wrapper. Pattern to
  emulate for executor-side wrappers.
- `turn/src/action.rs` — runtime `Effect` enum (line 427+).
- `turn/src/executor.rs::convert_turn_effects_to_vm` (line 2511) —
  the projection layer where executor's view of an effect becomes the
  AIR's PI vector.
- `circuit/src/effect_vm.rs::Effect` (line 927) — the Effect VM
  AIR's view of an effect.

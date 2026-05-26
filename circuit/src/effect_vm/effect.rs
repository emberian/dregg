//! The `Effect` enum: one variant per effect type the AIR proves.
//!
//! Each variant carries the witness data the trace generator needs to
//! emit the corresponding selector-gated row. Per-variant column
//! semantics live in `super::param`; per-variant AIR constraints live in
//! `super::air`.

use crate::field::BabyBear;

/// An effect to be proven in the VM.
#[derive(Clone, Debug)]
pub enum Effect {
    /// No operation (used for padding).
    NoOp,
    /// Transfer balance.
    Transfer {
        amount: u64,
        /// 0 = incoming (credit), 1 = outgoing (debit).
        direction: u32,
    },
    /// Set a custom field value.
    SetField { field_idx: u32, value: BabyBear },
    /// Grant a capability (add entry to c-list Merkle root).
    GrantCapability { cap_entry: BabyBear },
    /// Revoke a capability (mix the revoked slot's hash into the c-list Merkle root).
    /// Like `GrantCapability`, the AIR constraint enforces
    /// `new_cap_root == hash_2_to_1(old_cap_root, slot_hash)` so a malicious
    /// prover cannot make up an arbitrary new root.
    RevokeCapability { slot_hash: BabyBear },
    /// EmitEvent: stateless side-effect. Mirrors the runtime `Event` canonical
    /// encoding (topic ‖ data): `topic_hash` is the 32-byte BLAKE3 of the topic
    /// symbol, projected into 8 BabyBear felts (4 bytes per felt), and
    /// `payload_hash` is the 32-byte BLAKE3 of the concatenated `Vec<FieldElement>`
    /// data, projected the same way. Both contribute to `effects_hash`
    /// (binding the prover to the exact (topic, payload) bytes the executor
    /// observed), and the AIR additionally pins the low 4 felts of each into
    /// row params via a selector-gated PI-equality constraint (see
    /// `EMIT_EVENT_TOPIC_HASH` / `EMIT_EVENT_PAYLOAD_HASH` PI slots). The AIR
    /// constraint enforces full state passthrough — no balance, field, or
    /// cap_root change. Nonce increments by 1 like any non-NoOp effect.
    ///
    /// Soundness note: the per-row PI-equality constraint forces all
    /// emit-event rows in one proof to share the same (topic, payload) hashes.
    /// Multi-emit-distinct-hashes per proof is out of current scope; the
    /// off-AIR verifier's PI-match loop reads `EMIT_EVENT_COUNT` and refuses
    /// to derive multi-hash PI from the runtime turn (forcing the executor
    /// to split the turn into separate proofs if needed).
    EmitEvent {
        /// 32-byte BLAKE3 of the event topic symbol, projected into 8 BabyBear
        /// felts via 4-bytes-per-felt little-endian packing. Position 0 carries
        /// the low 4 bytes; position 7 the high 4 bytes.
        topic_hash: [BabyBear; 8],
        /// 32-byte BLAKE3 of the concatenated event data fields, same packing.
        payload_hash: [BabyBear; 8],
    },
    /// SetPermissions: update a cell's permission table. Permissions live
    /// outside the VM's tracked state, so the AIR enforces full state
    /// passthrough (balance / fields / cap_root unchanged) and the
    /// `permissions_hash` parameter binds the new permissions into
    /// effects_hash so the prover commits to the specific update.
    SetPermissions { permissions_hash: BabyBear },
    /// SetVerificationKey: update a cell's verification key (Option<VK>).
    /// Same shape as SetPermissions: VK lives off-trace, the AIR enforces
    /// state passthrough and `vk_hash` binds the new VK into effects_hash.
    /// `vk_hash == 0` represents "set to None" (revoke the VK).
    SetVerificationKey { vk_hash: BabyBear },
    /// CreateSealPair: register a new sealer/unsealer brand pair. Same
    /// passthrough shape; `pair_hash` is BLAKE3(sealer_holder ‖ unsealer_holder).
    CreateSealPair { pair_hash: BabyBear },
    /// RefreshDelegation: bump the delegation epoch. No params (the cell's
    /// epoch lives off-trace); selector alone records the intent. State
    /// passthrough.
    RefreshDelegation,
    /// RevokeDelegation: invalidate a child cell's delegation. State
    /// passthrough; `child_hash` binds the target cell into effects_hash.
    RevokeDelegation { child_hash: BabyBear },
    /// CreateCell: actor records the creation of a new cell. Passthrough.
    /// `create_hash` = BLAKE3(pk ‖ token_id ‖ balance) truncated to BabyBear.
    CreateCell { create_hash: BabyBear },
    /// SpawnWithDelegation: actor records spawning a child cell.
    /// `spawn_hash` = BLAKE3(child_pk ‖ child_token_id ‖ max_staleness).
    SpawnWithDelegation { spawn_hash: BabyBear },
    /// BridgeCancel: actor records the cancellation of a pending bridge.
    /// `nullifier_hash` binds the cancelled bridge into effects_hash.
    BridgeCancel { nullifier_hash: BabyBear },
    /// ExerciseViaCapability: actor records exercise of a c-list cap on a
    /// target cell. From the actor's perspective the actor's own state
    /// doesn't change; `exercise_hash` = BLAKE3(cap_slot ‖ inner_effects_hash).
    ExerciseViaCapability { exercise_hash: BabyBear },
    /// Introduce: 3-party introduction. Passthrough from the introducer's
    /// POV; `intro_hash` = BLAKE3(introducer ‖ recipient ‖ target ‖ perm).
    Introduce { intro_hash: BabyBear },
    /// PipelinedSend: dispatch a future action against an EventualRef.
    /// Passthrough; `send_hash` = BLAKE3(target.source_turn ‖ target.output_slot ‖ action.hash()).
    PipelinedSend { send_hash: BabyBear },
    /// CreateEscrow: actor's balance debits by `amount_lo`. Mirrors NoteCreate.
    /// `escrow_hash` = BLAKE3(recipient ‖ condition) binds the escrow target.
    ///
    /// 30-bit-trunc fix (CAVEAT-LAYER-COVERAGE.md §6.5): `amount_full` carries
    /// the full u64 amount; `amount_lo` retains its 30-bit-truncated form for
    /// backwards-compatible AIR constraint use (balance arithmetic uses
    /// `amount_lo` because the per-row balance limbs are 30+34-bit BabyBear).
    /// The trace generator pins `amount_full`'s 4×16-bit limb decomposition
    /// into `PI[CREATE_ESCROW_AMOUNT_LIMBS_BASE..+4]`; the verifier rejects
    /// any disagreement.
    CreateEscrow {
        amount_lo: BabyBear,
        escrow_hash: BabyBear,
        /// Full u64 amount (30-bit-trunc fix). Zero when this effect is
        /// absent from the trace. Multiple emissions sum (wrap-add).
        amount_full: u64,
    },
    /// BridgeLock: actor's balance debits by `value_lo`. Mirrors NoteCreate.
    /// `lock_hash` = BLAKE3(nullifier ‖ destination ‖ asset_type) binds the lock.
    ///
    /// 30-bit-trunc fix (CAVEAT-LAYER-COVERAGE.md §6.5): `value_full` carries
    /// the full u64 (see [`Effect::CreateEscrow`] above for rationale).
    BridgeLock {
        value_lo: BabyBear,
        lock_hash: BabyBear,
        /// Full u64 value (30-bit-trunc fix).
        value_full: u64,
    },
    /// CreateCommittedEscrow: passthrough; the locked amount is hidden in a
    /// Pedersen commitment that's verified outside this AIR.
    /// `commit_hash` = BLAKE3(creator_commit ‖ value_commit ‖ recipient_commit ‖ condition_commit).
    CreateCommittedEscrow { commit_hash: BabyBear },
    /// BridgeMint: actor mints `value_lo` from a portable proof. Balance
    /// credit (mirrors NoteSpend). `mint_hash` binds (nullifier, root,
    /// dest_federation, asset_type).
    ///
    /// 30-bit-trunc fix (CAVEAT-LAYER-COVERAGE.md §6.5): `value_full` carries
    /// the full u64 (see [`Effect::CreateEscrow`] above for rationale).
    BridgeMint {
        value_lo: BabyBear,
        mint_hash: BabyBear,
        /// Full u64 value (30-bit-trunc fix).
        value_full: u64,
    },
    /// BridgeFinalize: actor finalizes a pending bridge. Passthrough.
    /// `finalize_hash` = BLAKE3(nullifier ‖ receipt_bytes).
    BridgeFinalize { finalize_hash: BabyBear },
    /// ReleaseEscrow: passthrough; amount resolution requires escrow_id
    /// lookup in the ledger (out of AIR scope). `escrow_id_hash` binds
    /// which escrow was released.
    ReleaseEscrow { escrow_id_hash: BabyBear },
    /// RefundEscrow: passthrough; same shape as ReleaseEscrow.
    RefundEscrow { escrow_id_hash: BabyBear },
    /// ReleaseCommittedEscrow: passthrough; same shape, but
    /// `commit_hash` also binds the claim_auth + recipient.
    ReleaseCommittedEscrow { commit_hash: BabyBear },
    /// RefundCommittedEscrow: passthrough; same shape, binds claim_auth +
    /// creator.
    RefundCommittedEscrow { commit_hash: BabyBear },
    /// Spend a note (reveal nullifier, credit balance).
    NoteSpend { nullifier: BabyBear, value: u64 },
    /// Create a note (create commitment, debit balance).
    NoteCreate { commitment: BabyBear, value: u64 },
    /// Create a bonded obligation (locks stake from balance).
    /// Balance decreases by stake_amount. The obligation_id binds the terms.
    CreateObligation {
        /// Amount to lock.
        stake_amount: u64,
        /// Hash identifying the obligation terms (beneficiary, condition, deadline).
        obligation_id: BabyBear,
        /// Hash of the beneficiary cell.
        beneficiary_hash: BabyBear,
    },
    /// Fulfill an obligation (returns stake to obligor's balance).
    /// Balance increases by the returned stake amount.
    FulfillObligation {
        /// Hash identifying the obligation being fulfilled.
        obligation_id: BabyBear,
        /// Amount returned to obligor on fulfillment.
        stake_return: u64,
    },
    /// Custom cell program dispatch.
    ///
    /// State flows through normally (continuity enforced by the Effect VM).
    /// Domain-specific constraints are proven in a separate proof identified by
    /// `custom_proof_commitment`. The verifier checks that the external proof is
    /// valid and that its hash matches this commitment.
    Custom {
        /// VK hash identifying the custom program.
        ///
        /// **PI layout v2** (`pi::VK_PI_LAYOUT_VERSION == 2`): widened from
        /// 4 BabyBear felts (~16 bytes; 80-bit registry binding) to 8 felts
        /// (~32 bytes; ~248-bit registry binding) so that two custom programs
        /// whose 32-byte VKs collide only in the upper 16 bytes dispatch to
        /// distinct handlers. Pre-v2 callers zero-padded the upper 16 bytes,
        /// silently allowing such collisions to alias.
        program_vk_hash: [BabyBear; 8],
        /// Hash of the external custom program proof (4 BabyBear elements).
        proof_commitment: [BabyBear; 4],
    },
    /// Slash an expired obligation: transfer locked stake to beneficiary.
    /// Balance of beneficiary increases by stake_amount.
    SlashObligation {
        /// Hash identifying the obligation to slash.
        obligation_id: BabyBear,
        /// Amount slashed to beneficiary.
        stake_amount: u64,
        /// Hash of the beneficiary (for cap_root update).
        beneficiary_hash: BabyBear,
    },
    /// Seal: lock a field against mutation.
    /// Sets sealed_field_mask |= (1 << field_idx) in the reserved state slot.
    Seal {
        /// Index of field to seal (0..7).
        field_idx: u32,
    },
    /// Unseal: unlock a sealed field (requires brand matching via aux).
    /// Clears sealed_field_mask &= ~(1 << field_idx).
    Unseal {
        /// Index of field to unseal.
        field_idx: u32,
        /// Brand hash proving authority to unseal.
        brand: BabyBear,
    },
    /// MakeSovereign: transition cell mode from managed (0) to sovereign (1).
    /// State constraint: mode_flag changes from 0 to 1. Balance/fields preserved.
    MakeSovereign,
    /// CreateCellFromFactory: record factory VK hash + provenance.
    /// Uses aux columns for factory_vk and child_vk_derived.
    CreateCellFromFactory {
        /// Factory VK hash.
        factory_vk: BabyBear,
        /// Derived child VK hash (provenance record).
        child_vk_derived: BabyBear,
    },
    /// ExportSturdyRef: export a cell as a sturdy reference.
    /// Proves: swiss_number = Hash(cell_id || random_seed || export_counter).
    /// State transition: export_counter increments (tracked in field[7] by convention).
    ExportSturdyRef {
        /// Cell ID being exported.
        cell_id: BabyBear,
        /// Permissions mask.
        permissions: BabyBear,
        /// Random seed for swiss derivation.
        random_seed: BabyBear,
        /// Export counter (pre-increment value, stored in field[7]).
        export_counter: u32,
    },
    /// EnlivenRef: enliven a sturdy ref (validate swiss exists in table).
    /// Proves: swiss_number is a known swiss entry (via committed hash check).
    /// State transition: use_count increments (tracked in field[6] by convention).
    EnlivenRef {
        /// Swiss number to validate.
        swiss_number: BabyBear,
        /// Presenter ID.
        presenter_id: BabyBear,
        /// Expected cell_id from the swiss table entry.
        expected_cell_id: BabyBear,
        /// Expected permissions from the swiss table entry.
        expected_permissions: BabyBear,
    },
    /// DropRef: drop a remote reference (GC decrement).
    /// Proves: refcount > 0.
    /// State transition: refcount decrements (tracked in field[5] by convention).
    DropRef {
        /// Cell ID being released.
        cell_id: BabyBear,
        /// Federation hash of the holder.
        holder_federation: BabyBear,
        /// Current refcount (must be > 0).
        current_refcount: u32,
    },
    /// ValidateHandoff: validate a handoff certificate.
    /// Proves: certificate_hash is in the approved set (Merkle membership).
    /// Instead of in-circuit Ed25519, we prove set membership of the cert hash.
    /// State transition: routing entry created (cap_root updated).
    ValidateHandoff {
        /// Hash of the handoff certificate.
        certificate_hash: BabyBear,
        /// Recipient public key hash.
        recipient_pk: BabyBear,
        /// Introducer public key hash.
        introducer_pk: BabyBear,
        /// Merkle root of approved certificates set.
        approved_set_root: BabyBear,
    },
    /// AllocateQueue: create a new MerkleQueue (storage Phase 2).
    /// Proves: quota has sufficient balance for capacity * cost_per_slot.
    /// State transition: field[8] = queue_root set to empty_queue_hash,
    ///   field[9] = queue_capacity set. Balance debited by allocation cost.
    /// (field indices are logical; mapped to fields[0..7] + cap_root slot.)
    /// For the circuit, we use: cap_root stores empty_queue_hash (queue_root),
    /// and the capacity is stored in the reserved field's lower bits.
    /// Simplified: field[4] = queue_root (Poseidon2 empty hash), balance debited.
    AllocateQueue {
        /// Number of slots in the new queue.
        capacity: u32,
        /// Owner quota ID (for provenance).
        owner_quota_id: BabyBear,
        /// Cost per slot in computrons.
        cost_per_slot: u32,
    },
    /// EnqueueMessage: append a message hash to a queue.
    /// Proves: deposit >= min_deposit, queue is not full (queue_len < capacity).
    /// State transition: queue_root changes via hash chain (old_root -> new_root).
    /// If the queue has an attached program, the program validation hash is bound
    /// to the proof via aux[2].
    EnqueueMessage {
        /// Hash of the message being enqueued.
        message_hash: BabyBear,
        /// Deposit amount paid by sender.
        deposit_amount: u32,
        /// Sender ID.
        sender_id: BabyBear,
        /// Current queue length (pre-enqueue, must be < capacity for not-full check).
        queue_len: u32,
        /// Queue program VK hash as a BabyBear field element.
        /// ZERO if the queue has no attached program (backward compatible).
        /// Non-zero activates the program validation constraint.
        program_vk: BabyBear,
    },
    /// DequeueMessage: advance queue head, reveal expected message.
    /// Proves: message_hash matches head of queue (hash equality via aux).
    /// State transition: queue_root advances (head removed via hash chain).
    DequeueMessage {
        /// Expected message hash at head of queue.
        expected_message_hash: BabyBear,
        /// Deposit refund returned on dequeue.
        deposit_refund: u32,
    },
    /// ResizeQueue: change queue capacity.
    /// Proves: if growing, quota has balance for delta * cost_per_slot.
    /// State transition: capacity field updated, balance debited if growing.
    ResizeQueue {
        /// New capacity.
        new_capacity: u32,
        /// Queue ID.
        queue_id: BabyBear,
        /// Cost per slot (for balance check on grow).
        cost_per_slot: u32,
        /// Old capacity (for delta computation).
        old_capacity: u32,
    },
    /// AtomicQueueTx: prove an atomic cross-queue transaction.
    /// Proves: combined old roots -> combined new roots transition is valid,
    /// bound to a specific set of operations via tx_hash.
    /// State transition: field[4] transitions from combined_old_root to combined_new_root
    /// (proves ALL queues transitioned atomically; if ANY op fails, proof is invalid).
    /// Balance transition: balance changes by net_deposit (sum of deposits paid minus refunds).
    AtomicQueueTx {
        /// Number of operations in the transaction.
        op_count: u32,
        /// Hash of all operations (binds to specific ops).
        tx_hash: BabyBear,
        /// Combined old roots of all queues touched.
        combined_old_root: BabyBear,
        /// Combined new roots after atomic execution.
        combined_new_root: BabyBear,
        /// Net deposit paid across all sub-operations (deposits - refunds).
        /// Positive means balance decreases (net payment out).
        net_deposit: u32,
    },
    /// PipelineStep: prove a pipeline step correctly routed a message.
    /// Proves: message M was dequeued from source S and enqueued to sink K,
    /// per pipeline P. The proof covers a single routing step.
    /// State transition: field[4] (source root) transitions from source_old_root
    /// to source_new_root; aux[0] stores sink_new_root for external verification.
    PipelineStep {
        /// Pipeline identity hash (content-addressed from stage descriptions).
        pipeline_id: BabyBear,
        /// Source queue root before step.
        source_old_root: BabyBear,
        /// Source queue root after step (message dequeued).
        source_new_root: BabyBear,
        /// Sink queue root after step (message enqueued).
        sink_new_root: BabyBear,
        /// Message hash (what was routed).
        message_hash: BabyBear,
    },
    /// Burn: explicit, non-conservation reduction of the cell's balance.
    /// Unlike `Transfer { direction: 1 }`, no destination credit happens —
    /// the supply is provably reduced and the row is distinguishable from
    /// a Transfer at the algebraic level (selector + dedicated
    /// `was_burn_flag == 1` constraint).
    ///
    /// Relationship to `effect_action_air::SCHEMA_BURN`:
    ///   The two coexist as complementary attestations. `SCHEMA_BURN`
    ///   carries a per-`Effect::Burn` binding proof with the snapshot-
    ///   aware algebraic invariant `old_balance - new_balance == amount`
    ///   (executor-injected via `effect_binding_proofs`). This
    ///   `VmEffect::Burn` lives inside the cell's whole-turn Effect-VM
    ///   trace and attests "this Burn occupied row X in the cell's
    ///   effect sequence, distinct from any Transfer / NoteCreate".
    ///   The two layers cover different gaps; the SCHEMA_BURN remains
    ///   the canonical place for the balance-subtraction algebraic
    ///   binding.
    ///
    /// 30-bit-trunc note: `amount_lo` carries the low 30 bits for the
    /// balance-debit constraint (BabyBear can hold values < 2^31);
    /// `amount_full` carries the full u64 for `compute_effects_hash`
    /// binding via 4×16-bit limbs (matches the BridgeMint/BridgeLock
    /// shape).
    Burn {
        /// Hash of the target cell whose balance is reduced. Pinned to
        /// params[0] and folded into effects_hash so the proof binds to
        /// the specific cell.
        target_hash: BabyBear,
        /// Burn amount, low 30 bits (for the balance-debit constraint).
        amount_lo: BabyBear,
        /// Full u64 amount (binds via the 4×16-bit-limb path in
        /// `compute_effects_hash`).
        amount_full: u64,
    },
    /// CellDestroy: permanently retire a cell. Lifecycle lives off-trace,
    /// but the AIR binds the `target_hash` and the `death_certificate_hash`
    /// into params (and through them into effects_hash) so a verifier
    /// replaying the trace can distinguish a CellDestroy from a generic
    /// SetPermissions row.
    ///
    /// State passthrough: balance, fields, and cap_root all unchanged;
    /// nonce ticks like any non-NoOp effect.
    CellDestroy {
        /// Hash of the cell being destroyed.
        target_hash: BabyBear,
        /// `DeathCertificate::certificate_hash()` truncated to a BabyBear.
        death_certificate_hash: BabyBear,
    },
    /// AttenuateCapability: monotonically narrow an existing c-list cap.
    /// Distinct from RevokeCapability: revoke removes a slot from the
    /// c-list root by hashing `slot_hash` in; attenuate REPLACES the
    /// slot's existing entry with a strictly narrower commitment. The
    /// AIR's cap_root advance encodes BOTH the slot identity and the
    /// new narrower entry, so a `RevokeCapability` proof cannot pass as
    /// an `AttenuateCapability` proof.
    ///
    /// State: balance / fields unchanged; cap_root advances to
    /// `hash_2_to_1(old_cap_root, hash_2_to_1(cap_slot_hash, narrower_commitment))`.
    AttenuateCapability {
        /// Hash of the c-list slot being narrowed.
        cap_slot_hash: BabyBear,
        /// Commitment to the new (narrower) permissions / facet / expiry.
        narrower_commitment: BabyBear,
    },
}

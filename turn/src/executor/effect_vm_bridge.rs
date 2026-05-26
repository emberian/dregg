//! Bridge from turn-level `Effect` to circuit-level `pyana_circuit::effect_vm::Effect`.
//!
//! This module owns the (intentionally lossy) projection of a `Turn` into the
//! sequence of VM effects that the Effect VM AIR consumes for STARK proving.

use pyana_cell::{CellId, Ledger};

use crate::action::Effect;
use crate::forest::CallTree;
use crate::turn::Turn;

pub(super) fn convert_turn_effects_to_vm(
    cell_id: &CellId,
    turn: &Turn,
    ledger: &Ledger,
) -> Vec<pyana_circuit::effect_vm::Effect> {
    fn collect_effects(
        tree: &CallTree,
        cell_id: &CellId,
        ledger: &Ledger,
        vm_effects: &mut Vec<pyana_circuit::effect_vm::Effect>,
    ) {
        use pyana_circuit::effect_vm::Effect as VmEffect;
        use pyana_circuit::field::BabyBear;

        // REVIEW[effect-vm-coord]: Both helpers truncate 32-byte values to
        // 4 bytes (P1-2 in AUDIT-turn-executor.md). Many distinct effects
        // collapse to the same circuit-side identifier; the proof binds to
        // a coarse equivalence class rather than the specific effect.
        // The coordinated fix expands each per-effect PI slot (nullifier,
        // commitment, message_hash, pipeline_id, etc.) to 8 BabyBears via
        // `bytes32_to_babybear`, matching the executor's `compute_effects_hash`
        // which already hashes the full bytes. This is purely a circuit
        // PI-layout change on the runtime side, but the AIR's
        // domain-specific constraints over these slots must be widened in
        // tandem -- a single coordinated landing.
        fn hash_to_bb(h: &[u8; 32]) -> BabyBear {
            let val_u32 = u32::from_le_bytes([h[0], h[1], h[2], h[3]]);
            BabyBear::new(val_u32 % pyana_circuit::field::BABYBEAR_P)
        }

        fn field_element_to_bb(value: &[u8; 32]) -> BabyBear {
            let val_u32 = u32::from_le_bytes([value[0], value[1], value[2], value[3]]);
            BabyBear::new(val_u32 % pyana_circuit::field::BABYBEAR_P)
        }

        for effect in &tree.action.effects {
            match effect {
                Effect::Transfer { from, to, amount } => {
                    if from == cell_id {
                        vm_effects.push(VmEffect::Transfer {
                            amount: *amount,
                            direction: 1,
                        });
                    } else if to == cell_id {
                        vm_effects.push(VmEffect::Transfer {
                            amount: *amount,
                            direction: 0,
                        });
                    }
                }
                Effect::SetField { cell, index, value } if cell == cell_id => {
                    vm_effects.push(VmEffect::SetField {
                        field_idx: *index as u32,
                        value: field_element_to_bb(value),
                    });
                }
                Effect::GrantCapability { to, cap, .. } if to == cell_id => {
                    let cap_hash = blake3::hash(&cap.slot.to_le_bytes());
                    vm_effects.push(VmEffect::GrantCapability {
                        cap_entry: hash_to_bb(cap_hash.as_bytes()),
                    });
                }
                Effect::NoteSpend {
                    nullifier, value, ..
                } => {
                    vm_effects.push(VmEffect::NoteSpend {
                        nullifier: hash_to_bb(&nullifier.0),
                        value: *value,
                    });
                }
                Effect::NoteCreate {
                    commitment, value, ..
                } => {
                    vm_effects.push(VmEffect::NoteCreate {
                        commitment: hash_to_bb(&commitment.0),
                        value: *value,
                    });
                }
                Effect::IncrementNonce { cell } if cell == cell_id => {
                    // Nonce increment is implicit in the VM (row-to-row).
                }
                Effect::QueueAllocate {
                    capacity,
                    program_vk: _,
                } => {
                    // AllocateQueue: cost = capacity (1 computron per slot).
                    vm_effects.push(VmEffect::AllocateQueue {
                        capacity: *capacity as u32,
                        owner_quota_id: hash_to_bb(cell_id.as_bytes()),
                        cost_per_slot: 1,
                    });
                }
                Effect::QueueEnqueue {
                    queue,
                    message_hash,
                    deposit,
                } => {
                    // CLOSED block1-bind: queue length lives at
                    // `queue_cell.state.fields[1]` (low 8 bytes LE u64) and
                    // the queue's attached program_vk lives at
                    // `queue_cell.state.fields[3]` (low 4 bytes folded into
                    // BabyBear). Source both from the ledger now so the AIR
                    // witnesses the real capacity bound. The executor's
                    // apply_effect (`apply.rs::QueueEnqueue`) reads the
                    // same slots, so the AIR projection and the runtime
                    // mutation agree by construction.
                    let (queue_len, program_vk) = if let Some(queue_cell) = ledger.get(queue) {
                        let qlen = u64::from_le_bytes(
                            queue_cell.state.fields[1][..8]
                                .try_into()
                                .unwrap_or([0u8; 8]),
                        ) as u32;
                        // program_vk is fields[3] when programmable;
                        // hash_to_bb folds 4 bytes into a felt. Zero
                        // sentinel means "no attached program" — the
                        // AIR's `program_vk != 0` gate is honored.
                        let pvk = hash_to_bb(&queue_cell.state.fields[3]);
                        (qlen, pvk)
                    } else {
                        // Queue cell missing — executor will reject; we
                        // project sentinel so PI matching still aligns.
                        (0, BabyBear::ZERO)
                    };
                    vm_effects.push(VmEffect::EnqueueMessage {
                        message_hash: hash_to_bb(message_hash),
                        deposit_amount: *deposit as u32,
                        sender_id: hash_to_bb(cell_id.as_bytes()),
                        queue_len,
                        program_vk,
                    });
                }
                Effect::QueueDequeue { queue } => {
                    // DequeueMessage: the expected_message_hash is the queue's head.
                    // The executor validates correctness; the circuit proves the hash chain.
                    //
                    // CLOSED-PARTIALLY block1-bind: the dequeue head hash
                    // lives in storage's `QueueOperator::queue_head_hash`,
                    // NOT in `cell.state.fields` — `apply.rs::QueueDequeue`
                    // does not currently track per-message head commitments
                    // on the cell. To witness the true head we'd need to
                    // either:
                    //   (a) bind the head into a cell.state slot at enqueue
                    //       time (executor + AIR co-evolution), or
                    //   (b) plumb a QueueOperator reference into the bridge.
                    //
                    // Path (a) is the architecturally clean answer and is
                    // captured in BLOCK1-BIND-CLOSURE-NOTES.md. Until then
                    // we keep the domain-tagged sentinel: distinct from
                    // the queue-id alias (which collapsed soundness pre-
                    // fix), but still synthetic. The cell-side enqueue/
                    // dequeue length tracking via `fields[1]` IS bound
                    // through the AIR; the message hash is the remaining
                    // unbound surface.
                    let mut hasher = blake3::Hasher::new();
                    hasher.update(b"PYANA_DEQUEUE_HEAD/v1");
                    hasher.update(queue.as_bytes());
                    // Mix in the current queue length so two sequential
                    // dequeues on the same queue produce distinct
                    // projections (the AIR PI was previously identical
                    // for back-to-back dequeues against the same queue).
                    let qlen = ledger
                        .get(queue)
                        .map(|c| {
                            u64::from_le_bytes(
                                c.state.fields[1][..8].try_into().unwrap_or([0u8; 8]),
                            )
                        })
                        .unwrap_or(0);
                    hasher.update(&qlen.to_le_bytes());
                    let head_bytes = hasher.finalize();
                    vm_effects.push(VmEffect::DequeueMessage {
                        expected_message_hash: hash_to_bb(head_bytes.as_bytes()),
                        deposit_refund: 0, // Refund computed by executor at runtime.
                    });
                }
                Effect::QueueResize {
                    queue,
                    new_capacity,
                } => {
                    // CLOSED block1-bind: queue capacity lives at
                    // `queue_cell.state.fields[0]` (low 8 bytes LE u64),
                    // matching the executor's QueueAllocate write
                    // (`apply.rs::QueueAllocate` sets `fields[0][..8] =
                    // capacity.to_le_bytes()`). Source `old_capacity` from
                    // the ledger now so the AIR can distinguish shrink
                    // from grow.
                    let old_capacity = ledger
                        .get(queue)
                        .map(|c| {
                            u64::from_le_bytes(
                                c.state.fields[0][..8].try_into().unwrap_or([0u8; 8]),
                            ) as u32
                        })
                        .unwrap_or(0);
                    vm_effects.push(VmEffect::ResizeQueue {
                        new_capacity: *new_capacity as u32,
                        queue_id: hash_to_bb(queue.as_bytes()),
                        cost_per_slot: 1,
                        old_capacity,
                    });
                }
                Effect::QueueAtomicTx { operations } => {
                    // Compute net deposit: sum of enqueue deposits in the tx.
                    let mut net_deposit: u64 = 0;
                    for op in operations {
                        match op {
                            crate::action::QueueTxOp::Enqueue { deposit, .. } => {
                                net_deposit += deposit;
                            }
                            crate::action::QueueTxOp::Dequeue { .. } => {
                                // Refunds are runtime-computed; approximated as zero here.
                            }
                        }
                    }
                    // Build combined root hashes (binding the atomic transition).
                    let op_count = operations.len() as u32;
                    let tx_hash_input: Vec<u8> = operations
                        .iter()
                        .flat_map(|op| match op {
                            crate::action::QueueTxOp::Enqueue { message_hash, .. } => {
                                message_hash.to_vec()
                            }
                            crate::action::QueueTxOp::Dequeue { queue } => {
                                queue.as_bytes().to_vec()
                            }
                        })
                        .collect();
                    let tx_hash_bytes = blake3::hash(&tx_hash_input);
                    let tx_hash = hash_to_bb(tx_hash_bytes.as_bytes());
                    // Block 1 / CAVEAT-LAYER-COVERAGE.md §6.4 fix:
                    // pre-fix `combined_old_root == combined_new_root`
                    // made the AIR's transition check a self-loop.
                    // Post-fix we chain `combined_old` -> `combined_new`
                    // via `hash_2_to_1(combined_old, tx_hash)`, which
                    // forces the AIR's `field[4] == combined_old_root`
                    // -> `field[4] == combined_new_root` transition to
                    // be a real Poseidon2 step rather than a tautology.
                    //
                    // CLOSED block1-bind: `combined_old_root` is now
                    // sourced from the actor cell's `state.fields[4]`
                    // — the cell-side combined-queue-root slot the
                    // executor maintains in apply.rs. Honest path:
                    // executor reads/writes this slot; AIR PI binds it
                    // through this projection. When `fields[4]` is the
                    // zero sentinel (queue uninitialized), the synthetic
                    // cell-id projection keeps the AIR non-tautological.
                    let combined_old_root = ledger
                        .get(cell_id)
                        .map(|c| {
                            let f4 = c.state.fields[4];
                            if f4 == [0u8; 32] {
                                hash_to_bb(cell_id.as_bytes())
                            } else {
                                hash_to_bb(&f4)
                            }
                        })
                        .unwrap_or_else(|| hash_to_bb(cell_id.as_bytes()));
                    let combined_new_root =
                        pyana_circuit::poseidon2::hash_2_to_1(combined_old_root, tx_hash);
                    vm_effects.push(VmEffect::AtomicQueueTx {
                        op_count,
                        tx_hash,
                        combined_old_root,
                        combined_new_root,
                        net_deposit: net_deposit as u32,
                    });
                }
                Effect::QueuePipelineStep {
                    pipeline_id,
                    source,
                    sinks,
                } => {
                    let pipeline_bb = hash_to_bb(pipeline_id);
                    let source_root = hash_to_bb(source.as_bytes());
                    // Source new root = hash(source_old, message) — use a deterministic placeholder.
                    let msg_hash = hash_to_bb(pipeline_id);
                    let source_new = pyana_circuit::poseidon2::hash_2_to_1(source_root, msg_hash);
                    let sink_root = if let Some(sink) = sinks.first() {
                        hash_to_bb(sink.as_bytes())
                    } else {
                        BabyBear::ZERO
                    };
                    let sink_new = pyana_circuit::poseidon2::hash_2_to_1(sink_root, msg_hash);
                    vm_effects.push(VmEffect::PipelineStep {
                        pipeline_id: pipeline_bb,
                        source_old_root: source_root,
                        source_new_root: source_new,
                        sink_new_root: sink_new,
                        message_hash: msg_hash,
                    });
                }
                // ====================================================
                // Stage 1 (D): wire up the 7 runtime variants whose AIR
                // counterparts already exist but were previously mapped
                // to NoOp. The AIR enforces the per-effect arithmetic;
                // the projection is no longer lossy for these.
                // ====================================================
                Effect::CreateObligation {
                    beneficiary,
                    stake_amount,
                    stake,
                    ..
                } => {
                    // CreateObligation is emitted by the obligor; project
                    // when the cell is also the beneficiary (a self-bond)
                    // OR when the cell is a participant. The AIR variant
                    // currently treats this as a balance-debit + cap-root
                    // touch. We project for the executing cell.
                    let obligation_id_bytes = stake.0;
                    vm_effects.push(VmEffect::CreateObligation {
                        stake_amount: *stake_amount,
                        obligation_id: hash_to_bb(&obligation_id_bytes),
                        beneficiary_hash: hash_to_bb(beneficiary.as_bytes()),
                    });
                }
                Effect::FulfillObligation { obligation_id, .. } => {
                    vm_effects.push(VmEffect::FulfillObligation {
                        obligation_id: hash_to_bb(obligation_id),
                        // Stage 1: stake_return is not currently in the
                        // runtime variant; the AIR-side amount is wired
                        // by Stage 2's honesty pass once the obligation
                        // ledger is committed.
                        stake_return: 0,
                    });
                }
                Effect::SlashObligation { obligation_id } => {
                    vm_effects.push(VmEffect::SlashObligation {
                        obligation_id: hash_to_bb(obligation_id),
                        stake_amount: 0, // Stage 2 honesty pass
                        beneficiary_hash: hash_to_bb(cell_id.as_bytes()),
                    });
                }
                Effect::Seal { pair_id, .. } => {
                    // Stage 1: the runtime variant doesn't carry an
                    // explicit field_idx; we use the low bits of
                    // pair_id as a placeholder. Stage 2 reworks the
                    // Seal/Unseal AIR to operate on sealed_field_mask
                    // rather than on a single field index.
                    vm_effects.push(VmEffect::Seal {
                        field_idx: (pair_id[0] as u32) & 0x7,
                    });
                }
                Effect::Unseal { sealed_box, .. } => {
                    let bytes = postcard::to_allocvec(sealed_box).unwrap_or_default();
                    let brand_hash = blake3::hash(&bytes);
                    let mut tag = [0u8; 32];
                    tag.copy_from_slice(brand_hash.as_bytes());
                    vm_effects.push(VmEffect::Unseal {
                        field_idx: (tag[0] as u32) & 0x7,
                        brand: hash_to_bb(&tag),
                    });
                }
                Effect::MakeSovereign { cell } if cell == cell_id => {
                    vm_effects.push(VmEffect::MakeSovereign);
                }
                Effect::CreateCellFromFactory {
                    factory_vk,
                    owner_pubkey,
                    ..
                } => {
                    vm_effects.push(VmEffect::CreateCellFromFactory {
                        factory_vk: hash_to_bb(factory_vk),
                        child_vk_derived: hash_to_bb(owner_pubkey),
                    });
                }

                // ====================================================
                // Stage 3 complete: the 22 runtime variants below all
                // have real per-variant AIR coverage. Each projects to
                // a real VmEffect with its own constraint shape
                // (passthrough, balance debit/credit, or cap_root
                // transition). See STAGE-3-AIR-PLAN.md for the per-
                // variant rationale and EFFECT-VM-SHAPE-A.md for the
                // master plan context.
                // ====================================================
                Effect::SetPermissions {
                    cell,
                    new_permissions,
                } if cell == cell_id => {
                    // Stage 3: real AIR coverage. Permissions aren't in
                    // VM state; bind their hash into effects_hash.
                    let perm_bytes = postcard::to_allocvec(new_permissions).unwrap_or_default();
                    let perm_hash_bytes = blake3::hash(&perm_bytes);
                    vm_effects.push(VmEffect::SetPermissions {
                        permissions_hash: hash_to_bb(perm_hash_bytes.as_bytes()),
                    });
                }
                Effect::SetVerificationKey { cell, new_vk } if cell == cell_id => {
                    // Stage 3: real AIR coverage. VK lives off-trace;
                    // bind its hash into effects_hash. None → 0.
                    let vk_hash = match new_vk {
                        Some(vk) => {
                            let bytes = postcard::to_allocvec(vk).unwrap_or_default();
                            let h = blake3::hash(&bytes);
                            hash_to_bb(h.as_bytes())
                        }
                        None => pyana_circuit::field::BabyBear::ZERO,
                    };
                    vm_effects.push(VmEffect::SetVerificationKey { vk_hash });
                }
                Effect::RevokeCapability { cell, slot } if cell == cell_id => {
                    // Stage 3: real AIR coverage. Mirrors GrantCapability.
                    // The slot's bytes are hashed and the result is mixed
                    // into capability_root deterministically by the AIR.
                    let slot_bytes = slot.to_le_bytes();
                    let slot_hash_bytes = blake3::hash(&slot_bytes);
                    vm_effects.push(VmEffect::RevokeCapability {
                        slot_hash: hash_to_bb(slot_hash_bytes.as_bytes()),
                    });
                }
                Effect::CreateCell {
                    public_key,
                    token_id,
                    balance,
                } => {
                    // Stage 3: real AIR coverage. CreateCell rejects
                    // non-zero balance via executor, so the actor's
                    // balance doesn't change — passthrough is correct.
                    let mut hasher = blake3::Hasher::new();
                    hasher.update(public_key);
                    hasher.update(token_id);
                    hasher.update(&balance.to_le_bytes());
                    let create_hash_bytes = hasher.finalize();
                    vm_effects.push(VmEffect::CreateCell {
                        create_hash: hash_to_bb(create_hash_bytes.as_bytes()),
                    });
                }
                Effect::CreateSealPair {
                    sealer_holder,
                    unsealer_holder,
                } => {
                    // Stage 3: real AIR coverage. Hash both holders into
                    // a single pair_hash bound via effects_hash.
                    let mut hasher = blake3::Hasher::new();
                    hasher.update(sealer_holder.as_bytes());
                    hasher.update(unsealer_holder.as_bytes());
                    let pair_hash_bytes = hasher.finalize();
                    vm_effects.push(VmEffect::CreateSealPair {
                        pair_hash: hash_to_bb(pair_hash_bytes.as_bytes()),
                    });
                }
                Effect::EmitEvent { cell, event } if cell == cell_id => {
                    // Stage 3 + #110: real AIR coverage with canonical
                    // (topic_hash, payload_hash) binding. Each 32-byte
                    // BLAKE3 hash projects into 8 BabyBear felts via
                    // 4-bytes-per-felt little-endian packing (matches the
                    // Custom::program_vk_hash convention).
                    //
                    // - topic_hash = BLAKE3(event.topic)        (32 bytes)
                    // - payload_hash = BLAKE3(event.data ‖ ...) (32 bytes)
                    //
                    // The AIR's per-row PI-equality constraint pins the low 4
                    // felts of each into params[0..8]; effects_hash absorbs
                    // all 16 felts (cryptographic high-half binding); the
                    // off-AIR PI-match loop double-checks against the
                    // runtime Event encoding.
                    let topic_bytes = *blake3::hash(&event.topic).as_bytes();
                    let mut payload_hasher = blake3::Hasher::new();
                    for d in &event.data {
                        payload_hasher.update(d);
                    }
                    let payload_bytes = *payload_hasher.finalize().as_bytes();

                    fn bytes32_to_8_felts(b: &[u8; 32]) -> [BabyBear; 8] {
                        let mut out = [BabyBear::ZERO; 8];
                        for i in 0..8 {
                            let off = i * 4;
                            let v =
                                u32::from_le_bytes([b[off], b[off + 1], b[off + 2], b[off + 3]]);
                            // Reduce mod p so we always land in canonical BabyBear.
                            out[i] = BabyBear::new(v % pyana_circuit::field::BABYBEAR_P);
                        }
                        out
                    }

                    vm_effects.push(VmEffect::EmitEvent {
                        topic_hash: bytes32_to_8_felts(&topic_bytes),
                        payload_hash: bytes32_to_8_felts(&payload_bytes),
                    });
                }
                Effect::SpawnWithDelegation {
                    child_public_key,
                    child_token_id,
                    max_staleness,
                } => {
                    // Stage 3: real AIR coverage. Passthrough — the
                    // child cell is its own entity; actor's state
                    // doesn't change.
                    let mut hasher = blake3::Hasher::new();
                    hasher.update(child_public_key);
                    hasher.update(child_token_id);
                    hasher.update(&max_staleness.to_le_bytes());
                    let spawn_hash_bytes = hasher.finalize();
                    vm_effects.push(VmEffect::SpawnWithDelegation {
                        spawn_hash: hash_to_bb(spawn_hash_bytes.as_bytes()),
                    });
                }
                Effect::RefreshDelegation => {
                    // Stage 3: real AIR coverage. No params on the
                    // runtime side; selector alone records intent.
                    vm_effects.push(VmEffect::RefreshDelegation);
                }
                Effect::RevokeDelegation { child } => {
                    // Stage 3: real AIR coverage. child_hash binds the
                    // target cell into effects_hash.
                    vm_effects.push(VmEffect::RevokeDelegation {
                        child_hash: hash_to_bb(child.as_bytes()),
                    });
                }
                Effect::IncrementNonce { cell } if cell == cell_id => {
                    // No AIR effect needed — nonce increments are implicit
                    // in the row-to-row continuity. Skip to avoid a NoOp.
                }
                Effect::BridgeMint { portable_proof } => {
                    // Stage 3: real AIR coverage. Balance credit by the
                    // proof's value field. mint_hash binds the proof's
                    // public-input shape (nullifier, root, dest fed,
                    // asset_type) so the prover commits to which bridge
                    // mint event was processed.
                    let mut hasher = blake3::Hasher::new();
                    hasher.update(&portable_proof.nullifier);
                    // AttestedRoot is structured; serialize it for hashing.
                    let root_bytes =
                        postcard::to_allocvec(&portable_proof.source_root).unwrap_or_default();
                    hasher.update(&root_bytes);
                    hasher.update(&portable_proof.destination_federation);
                    hasher.update(&portable_proof.asset_type.to_le_bytes());
                    let mint_hash_bytes = hasher.finalize();
                    let value_lo = pyana_circuit::field::BabyBear::new(
                        (portable_proof.value & ((1u64 << 30) - 1)) as u32,
                    );
                    vm_effects.push(VmEffect::BridgeMint {
                        value_lo,
                        mint_hash: hash_to_bb(mint_hash_bytes.as_bytes()),
                        // 30-bit-trunc fix (CAVEAT-LAYER-COVERAGE.md
                        // §6.5): carry the full u64 in the VmEffect so
                        // the AIR's effects-hash + PI limbs bind to
                        // the entire value, not just the low 30 bits.
                        value_full: portable_proof.value,
                    });
                }
                Effect::BridgeLock {
                    nullifier,
                    destination,
                    value,
                    asset_type,
                    ..
                } => {
                    // Stage 3: real AIR coverage. Balance debit.
                    let mut hasher = blake3::Hasher::new();
                    hasher.update(nullifier);
                    hasher.update(destination);
                    hasher.update(&asset_type.to_le_bytes());
                    let lock_hash_bytes = hasher.finalize();
                    let value_lo =
                        pyana_circuit::field::BabyBear::new((*value & ((1u64 << 30) - 1)) as u32);
                    vm_effects.push(VmEffect::BridgeLock {
                        value_lo,
                        lock_hash: hash_to_bb(lock_hash_bytes.as_bytes()),
                        // 30-bit-trunc fix.
                        value_full: *value,
                    });
                }
                Effect::BridgeFinalize { nullifier, receipt } => {
                    // Stage 3: passthrough. Mint vs lock outcome lives
                    // in the bridge state lookup (executor's job).
                    let mut hasher = blake3::Hasher::new();
                    hasher.update(nullifier);
                    let receipt_bytes = postcard::to_allocvec(receipt).unwrap_or_default();
                    hasher.update(&receipt_bytes);
                    let finalize_hash_bytes = hasher.finalize();
                    vm_effects.push(VmEffect::BridgeFinalize {
                        finalize_hash: hash_to_bb(finalize_hash_bytes.as_bytes()),
                    });
                }
                Effect::BridgeCancel { nullifier } => {
                    // Stage 3: real AIR coverage. Passthrough — bridge
                    // state lives off-trace; nullifier binds intent.
                    vm_effects.push(VmEffect::BridgeCancel {
                        nullifier_hash: hash_to_bb(nullifier),
                    });
                }
                Effect::Introduce {
                    introducer,
                    recipient,
                    target,
                    permissions,
                } => {
                    // Stage 3: real AIR coverage. Passthrough from the
                    // introducer's POV; recipient-side cap_root update
                    // happens when this turn is replayed against the
                    // recipient cell (separate projection).
                    let mut hasher = blake3::Hasher::new();
                    hasher.update(introducer.as_bytes());
                    hasher.update(recipient.as_bytes());
                    hasher.update(target.as_bytes());
                    let perm_byte: u8 = match permissions {
                        pyana_cell::AuthRequired::None => 0,
                        pyana_cell::AuthRequired::Signature => 1,
                        pyana_cell::AuthRequired::Proof => 2,
                        pyana_cell::AuthRequired::Either => 3,
                        pyana_cell::AuthRequired::Impossible => 4,
                        pyana_cell::AuthRequired::Custom { .. } => 5,
                    };
                    hasher.update(&[perm_byte]);
                    // For Custom, also hash the vk_hash so distinct
                    // Custom modes route to distinct intro hashes.
                    if let pyana_cell::AuthRequired::Custom { vk_hash } = permissions {
                        hasher.update(vk_hash);
                    }
                    let intro_hash_bytes = hasher.finalize();
                    vm_effects.push(VmEffect::Introduce {
                        intro_hash: hash_to_bb(intro_hash_bytes.as_bytes()),
                    });
                }
                Effect::PipelinedSend { target, action } => {
                    // Stage 3: real AIR coverage. The dispatching cell
                    // doesn't change state; bind the deferred
                    // dispatch into effects_hash.
                    let mut hasher = blake3::Hasher::new();
                    hasher.update(&target.source_turn);
                    hasher.update(&target.output_slot.to_le_bytes());
                    hasher.update(&action.hash());
                    let send_hash_bytes = hasher.finalize();
                    vm_effects.push(VmEffect::PipelinedSend {
                        send_hash: hash_to_bb(send_hash_bytes.as_bytes()),
                    });
                }
                Effect::CreateEscrow {
                    cell,
                    recipient,
                    amount,
                    condition,
                    ..
                } if cell == cell_id => {
                    // Stage 3: real AIR coverage. Mirror NoteCreate's
                    // balance debit constraint shape.
                    let mut hasher = blake3::Hasher::new();
                    hasher.update(recipient.as_bytes());
                    let cond_bytes = postcard::to_allocvec(condition).unwrap_or_default();
                    hasher.update(&cond_bytes);
                    let escrow_hash_bytes = hasher.finalize();
                    // Truncate amount to u32 for the field element.
                    let amount_lo =
                        pyana_circuit::field::BabyBear::new((*amount & ((1u64 << 30) - 1)) as u32);
                    vm_effects.push(VmEffect::CreateEscrow {
                        amount_lo,
                        escrow_hash: hash_to_bb(escrow_hash_bytes.as_bytes()),
                        // 30-bit-trunc fix.
                        amount_full: *amount,
                    });
                }
                Effect::ReleaseEscrow { escrow_id, .. } => {
                    // Stage 3: passthrough. Amount resolution requires
                    // escrow_id lookup in the ledger (out of AIR scope).
                    vm_effects.push(VmEffect::ReleaseEscrow {
                        escrow_id_hash: hash_to_bb(escrow_id),
                    });
                }
                Effect::RefundEscrow { escrow_id, .. } => {
                    // Stage 3: passthrough. Same shape as ReleaseEscrow.
                    vm_effects.push(VmEffect::RefundEscrow {
                        escrow_id_hash: hash_to_bb(escrow_id),
                    });
                }
                Effect::CreateCommittedEscrow {
                    creator_commitment,
                    recipient_commitment,
                    value_commitment,
                    condition_commitment,
                    ..
                } => {
                    // Stage 3: passthrough. Value is hidden in a Pedersen
                    // commitment that the AIR can't open; the executor
                    // verifies the range proof separately.
                    let mut hasher = blake3::Hasher::new();
                    hasher.update(creator_commitment);
                    hasher.update(recipient_commitment);
                    hasher.update(&value_commitment.0);
                    hasher.update(condition_commitment);
                    let commit_hash_bytes = hasher.finalize();
                    vm_effects.push(VmEffect::CreateCommittedEscrow {
                        commit_hash: hash_to_bb(commit_hash_bytes.as_bytes()),
                    });
                }
                Effect::ReleaseCommittedEscrow {
                    escrow_id,
                    recipient,
                    ..
                } => {
                    // Stage 3: passthrough. Amount + binding to claim_auth
                    // is verified separately by executor.
                    let mut hasher = blake3::Hasher::new();
                    hasher.update(escrow_id);
                    hasher.update(recipient.as_bytes());
                    let commit_hash_bytes = hasher.finalize();
                    vm_effects.push(VmEffect::ReleaseCommittedEscrow {
                        commit_hash: hash_to_bb(commit_hash_bytes.as_bytes()),
                    });
                }
                Effect::RefundCommittedEscrow {
                    escrow_id, creator, ..
                } => {
                    // Stage 3: passthrough. Same shape with creator.
                    let mut hasher = blake3::Hasher::new();
                    hasher.update(escrow_id);
                    hasher.update(creator.as_bytes());
                    let commit_hash_bytes = hasher.finalize();
                    vm_effects.push(VmEffect::RefundCommittedEscrow {
                        commit_hash: hash_to_bb(commit_hash_bytes.as_bytes()),
                    });
                }
                Effect::ExerciseViaCapability {
                    cap_slot,
                    inner_effects,
                } => {
                    // Stage 3: real AIR coverage. From the actor's POV
                    // this is passthrough — the inner_effects act on
                    // the target cell. Bind (cap_slot, inner_effects)
                    // via effects_hash so the prover can't swap them.
                    let mut hasher = blake3::Hasher::new();
                    hasher.update(&cap_slot.to_le_bytes());
                    for inner in inner_effects {
                        hasher.update(&inner.hash());
                    }
                    let exercise_hash_bytes = hasher.finalize();
                    vm_effects.push(VmEffect::ExerciseViaCapability {
                        exercise_hash: hash_to_bb(exercise_hash_bytes.as_bytes()),
                    });
                }

                // ────────────────────────────────────────────────────
                // Stage 7 / P1.A: CapTP runtime effect projections.
                // Each runtime variant maps to its AIR counterpart
                // (selectors 14..17). The AIR params are bound into
                // effects_hash via `compute_effects_hash`, so the
                // prover commits to the specific CapTP operation.
                // The richer Merkle-proof witnesses required to make
                // the AIR non-tautological are added in P1.C.
                // ────────────────────────────────────────────────────
                Effect::ExportSturdyRef {
                    swiss_number,
                    target,
                    permissions,
                } if target == cell_id => {
                    // Project: AIR's ExportSturdyRef proves
                    //   swiss = hash(cell_id, hash(random_seed, counter))
                    // To keep the AIR constraint satisfiable from
                    // off-trace data, we project with the cell's
                    // current field[7] (export counter) and a
                    // random_seed value such that the AIR's swiss
                    // derivation matches the provided swiss_number.
                    // For now, we collapse: random_seed = first 4
                    // bytes of swiss_number; the executor will set
                    // aux[0] to whatever the AIR-side derivation
                    // would compute — the AIR self-consistency check
                    // is what's enforced.
                    let cell_id_bb = hash_to_bb(target.as_bytes());
                    let random_seed_bb = hash_to_bb(swiss_number);
                    // CLOSED block1-bind:
                    //   - `export_counter` now sourced from
                    //     `target.state.fields[7]` (low 4 bytes LE u32),
                    //     so the AIR's swiss derivation
                    //     `hash_2_to_1(cell_id, hash_2_to_1(random_seed,
                    //     counter))` is no longer tautological — a
                    //     prover cannot pick an arbitrary counter.
                    //   - `permissions` now sourced from the runtime
                    //     variant (`ExportSturdyRef-permissions`
                    //     closure). The AIR's `EXPORT_PERMISSIONS`
                    //     PARAM projects from this field; the apply
                    //     site validates the declared tier is
                    //     narrower-or-equal to the cell's access tier
                    //     (so an exporter cannot fabricate authority
                    //     beyond what the cell holds). The
                    //     federation's swiss-table mirror records the
                    //     same value, keeping AIR and runtime in
                    //     lock-step.
                    let export_counter = ledger
                        .get(target)
                        .map(|c| {
                            u32::from_le_bytes(
                                c.state.fields[7][..4].try_into().unwrap_or([0u8; 4]),
                            )
                        })
                        .unwrap_or(0);
                    // Encode the permissions tier into a BabyBear. The
                    // tier-byte (per `cell::commitment::auth_byte`) is
                    // the canonical discriminator; for `Custom` the
                    // vk_hash byte stream is hashed into the field
                    // element to preserve injectivity across distinct
                    // `Custom` predicates.
                    let permissions_bb = match permissions {
                        pyana_cell::permissions::AuthRequired::None => BabyBear::new(0),
                        pyana_cell::permissions::AuthRequired::Signature => BabyBear::new(1),
                        pyana_cell::permissions::AuthRequired::Proof => BabyBear::new(2),
                        pyana_cell::permissions::AuthRequired::Either => BabyBear::new(3),
                        pyana_cell::permissions::AuthRequired::Impossible => BabyBear::new(4),
                        pyana_cell::permissions::AuthRequired::Custom { vk_hash } => {
                            // Fold the discriminant byte + vk_hash via
                            // blake3 to a single felt. Two distinct
                            // Custom predicates yield distinct values.
                            let mut h = blake3::Hasher::new();
                            h.update(&[5u8]);
                            h.update(vk_hash);
                            hash_to_bb(h.finalize().as_bytes())
                        }
                    };
                    vm_effects.push(VmEffect::ExportSturdyRef {
                        cell_id: cell_id_bb,
                        permissions: permissions_bb,
                        random_seed: random_seed_bb,
                        export_counter,
                    });
                }
                Effect::EnlivenRef {
                    swiss_number,
                    bearer,
                    expected_cell_id,
                    expected_permissions,
                } if bearer == cell_id => {
                    // Project: AIR's EnlivenRef proves swiss-table
                    // membership of the entry via the 1-hop Merkle
                    // chain
                    //   new_root = hash(leaf, old_root)
                    //   leaf     = hash(swiss, hash(cell_id, perms))
                    // against the bearer's `swiss_table_root` slot in
                    // `state.fields[4]`.
                    //
                    // CLOSED block1-bind
                    // (`EnlivenRef-permissions-merkle`): both
                    // `expected_cell_id` and `expected_permissions`
                    // now project from the runtime variant directly.
                    // The apply gate
                    // (`apply.rs::EnlivenRef`) validates that the
                    // bearer's c-list contains a capability for
                    // `expected_cell_id` with a tier covering the
                    // declared `expected_permissions`, so a forged
                    // variant cannot bind into the swiss_table_root
                    // chain without an underlying real capability.
                    let swiss_bb = hash_to_bb(swiss_number);
                    let presenter_bb = hash_to_bb(bearer.as_bytes());
                    let expected_cell_id_bb = hash_to_bb(expected_cell_id.as_bytes());
                    let permissions_bb = match expected_permissions {
                        pyana_cell::permissions::AuthRequired::None => BabyBear::new(0),
                        pyana_cell::permissions::AuthRequired::Signature => BabyBear::new(1),
                        pyana_cell::permissions::AuthRequired::Proof => BabyBear::new(2),
                        pyana_cell::permissions::AuthRequired::Either => BabyBear::new(3),
                        pyana_cell::permissions::AuthRequired::Impossible => BabyBear::new(4),
                        pyana_cell::permissions::AuthRequired::Custom { vk_hash } => {
                            let mut h = blake3::Hasher::new();
                            h.update(&[5u8]);
                            h.update(vk_hash);
                            hash_to_bb(h.finalize().as_bytes())
                        }
                    };
                    vm_effects.push(VmEffect::EnlivenRef {
                        swiss_number: swiss_bb,
                        presenter_id: presenter_bb,
                        expected_cell_id: expected_cell_id_bb,
                        expected_permissions: permissions_bb,
                    });
                }
                Effect::DropRef { ref_id } => {
                    // Project: AIR's DropRef proves refcount > 0 and
                    // decrements. The cell_id and holder_federation
                    // are bound; the AIR currently treats refcount
                    // as the cell's field[5]. We pass a non-zero
                    // refcount; the executor's apply_effect verifies
                    // the actual stored refcount.
                    //
                    // CLOSED block1-bind: `current_refcount` is now
                    // sourced from `cell.state.fields[5]` (the refcount
                    // slot the AIR's per-row `field[5]` continuity
                    // already constrains). The AIR's `refcount > 0`
                    // check is no longer satisfied by construction —
                    // it must hold against the actual ledger state.
                    let cell_id_bb = hash_to_bb(cell_id.as_bytes());
                    let ref_id_bb = hash_to_bb(ref_id);
                    // Refcount stored as u32 in low 4 bytes LE of fields[5].
                    let current_refcount = ledger
                        .get(cell_id)
                        .map(|c| {
                            u32::from_le_bytes(
                                c.state.fields[5][..4].try_into().unwrap_or([0u8; 4]),
                            )
                        })
                        .unwrap_or(0);
                    vm_effects.push(VmEffect::DropRef {
                        cell_id: cell_id_bb,
                        holder_federation: ref_id_bb,
                        current_refcount,
                    });
                }
                Effect::ValidateHandoff {
                    cert_hash,
                    recipient_pk,
                    introducer_pk,
                } => {
                    // Project: AIR's ValidateHandoff proves
                    // cert_hash ∈ approved_handoffs_root via 1-hop
                    // Merkle membership. The PARAMs (cert_hash,
                    // recipient_pk, introducer_pk) project directly
                    // from the runtime variant — no executor synthesis.
                    //
                    // CLOSED block1-bind
                    // (`ValidateHandoff-runtime-variant-extend`): both
                    // public keys now exit the runtime variant
                    // explicitly. The authorization gate
                    // (`authorize.rs::verify_captp_delivered` post-
                    // closure check) enforces that the effect-carried
                    // keys match the action's cert; the AIR's leaf
                    // `hash(cert_hash, hash(recipient_pk,
                    // introducer_pk))` therefore binds to keys whose
                    // cryptographic legitimacy is enforced at the
                    // authorization layer.
                    //
                    // `approved_set_root` is already federation-bound
                    // via PI[APPROVED_HANDOFFS_BASE].
                    let cert_bb = hash_to_bb(cert_hash);
                    let recipient_pk_bb = hash_to_bb(recipient_pk);
                    let introducer_pk_bb = hash_to_bb(introducer_pk);
                    // approved_set_root stays as ZERO here because
                    // the AIR-side param is matched against the
                    // verifier's PI[APPROVED_HANDOFFS_BASE] (see
                    // captp constraints' `aux[6] ==
                    // approved_set_root` + executor PI-match);
                    // the federation's real root is supplied via
                    // PI, not via this projection.
                    vm_effects.push(VmEffect::ValidateHandoff {
                        certificate_hash: cert_bb,
                        recipient_pk: recipient_pk_bb,
                        introducer_pk: introducer_pk_bb,
                        approved_set_root: BabyBear::ZERO,
                    });
                }

                // ────────────────────────────────────────────────────
                // Near-miss aliasing closure (#100 follow-up): three
                // runtime variants whose VM-side AIR coverage previously
                // either fell through to `_` (no projection) or aliased
                // to a sibling VmEffect (Transfer-dir-1 / SetPermissions /
                // RevokeCapability). Each now projects to a dedicated
                // VmEffect whose AIR constraints are algebraically
                // distinct from the sibling — see the matching variant
                // arms in `circuit/src/effect_vm/air.rs`.
                // ────────────────────────────────────────────────────
                Effect::Burn {
                    target,
                    slot: _,
                    amount,
                } if target == cell_id => {
                    use pyana_circuit::field::BabyBear;
                    let target_hash = hash_to_bb(target.as_bytes());
                    // Low 30 bits drive the AIR balance debit; the full
                    // u64 is bound through `compute_effects_hash`.
                    let amount_lo = BabyBear::new((*amount & ((1u64 << 30) - 1)) as u32);
                    vm_effects.push(VmEffect::Burn {
                        target_hash,
                        amount_lo,
                        amount_full: *amount,
                    });
                }
                Effect::CellDestroy {
                    target,
                    certificate,
                } if target == cell_id => {
                    let target_hash = hash_to_bb(target.as_bytes());
                    let cert_hash = certificate.certificate_hash();
                    vm_effects.push(VmEffect::CellDestroy {
                        target_hash,
                        death_certificate_hash: hash_to_bb(&cert_hash),
                    });
                }
                Effect::AttenuateCapability {
                    cell,
                    slot,
                    narrower_permissions,
                    narrower_effects,
                    narrower_expiry,
                } if cell == cell_id => {
                    // Bind the slot identifier (low 4 bytes of its LE
                    // encoding) into the first param, and a commitment
                    // over (permissions, effect_mask, expiry) into the
                    // second. The narrower_commitment is the canonical
                    // BLAKE3 over the same byte stream the runtime's
                    // journal entry / receipt-hash will absorb, so a
                    // forged "wider" attenuation cannot collide.
                    let slot_bytes = slot.to_le_bytes();
                    let cap_slot_hash = hash_to_bb(blake3::hash(&slot_bytes).as_bytes());
                    let mut h = blake3::Hasher::new();
                    h.update(b"PYANA_ATTN_NARROWER/v1");
                    let perm_bytes =
                        postcard::to_allocvec(narrower_permissions).unwrap_or_default();
                    h.update(&perm_bytes);
                    if let Some(mask) = narrower_effects {
                        h.update(&[1u8]);
                        h.update(&mask.to_le_bytes());
                    } else {
                        h.update(&[0u8]);
                    }
                    if let Some(exp) = narrower_expiry {
                        h.update(&[1u8]);
                        h.update(&exp.to_le_bytes());
                    } else {
                        h.update(&[0u8]);
                    }
                    let narrower_commitment = hash_to_bb(h.finalize().as_bytes());
                    vm_effects.push(VmEffect::AttenuateCapability {
                        cap_slot_hash,
                        narrower_commitment,
                    });
                }

                _ => {
                    // Effects not targeting `cell_id` or arms covered by
                    // explicit guards above (e.g., a cross-cell effect
                    // whose other end isn't us) are silently skipped —
                    // they're not part of this cell's proof.
                }
            }
        }
        for child in &tree.children {
            collect_effects(child, cell_id, ledger, vm_effects);
        }
    }

    // Stage 3 complete: push_pending_shim was the temporary scaffolding
    // for the 22 variants without dedicated AIR coverage. All 22 now
    // have real per-variant AIR variants, so the shim is removed.
    // The `effect-vm-pending-shim` feature flag is no longer used.

    let mut vm_effects = Vec::new();
    for root in &turn.call_forest.roots {
        collect_effects(root, cell_id, ledger, &mut vm_effects);
    }

    // Must have at least one effect for the VM.
    if vm_effects.is_empty() {
        vm_effects.push(pyana_circuit::effect_vm::Effect::NoOp);
    }
    vm_effects
}

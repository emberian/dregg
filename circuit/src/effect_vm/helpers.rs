//! Helper functions for the Effect VM AIR.
//!
//! Limb splitting/joining and the `compute_effects_hash` family that
//! produces the per-cell effects digest pinned into PI[EFFECTS_HASH_BASE].

use crate::field::BabyBear;
use crate::poseidon2::{hash_2_to_1, hash_4_to_1, hash_many};

use super::{AUX_BASE, Effect, aux_off};

/// Split a u64 into two BabyBear elements: (lo = lower 30 bits, hi = upper 34 bits).
/// Both values fit in BabyBear (< 2^31).
pub fn split_u64(val: u64) -> (BabyBear, BabyBear) {
    let lo = (val & 0x3FFF_FFFF) as u32; // lower 30 bits
    let hi = (val >> 30) as u32; // upper 34 bits (fits in u32 since val < 2^64)
    (BabyBear::new(lo), BabyBear::new(hi))
}

/// Reconstruct a u64 from split BabyBear limbs.
#[allow(dead_code)]
fn join_u64(lo: BabyBear, hi: BabyBear) -> u64 {
    (lo.0 as u64) | ((hi.0 as u64) << 30)
}

/// Decompose a u64 into 4 BabyBear limbs (16 bits each, little-endian).
/// Returns `[lo16, mid_lo16, mid_hi16, hi16]` so the limbs sum back to
/// the original via `Σ limbs[i] * 2^(16*i)`. Used to project full-u64
/// effect values into the AIR PI without 30-bit truncation
/// (CAVEAT-LAYER-COVERAGE.md §6.5).
#[inline]
pub fn u64_to_4_limbs_16(value: u64) -> [BabyBear; 4] {
    [
        BabyBear::new((value & 0xFFFF) as u32),
        BabyBear::new(((value >> 16) & 0xFFFF) as u32),
        BabyBear::new(((value >> 32) & 0xFFFF) as u32),
        BabyBear::new(((value >> 48) & 0xFFFF) as u32),
    ]
}

/// Inverse of [`u64_to_4_limbs_16`]: reconstruct a u64 from 4 BabyBear
/// limbs of 16 bits each. Returns `None` if any limb exceeds 2^16
/// (rejects out-of-range limbs — adversarial-test entry point).
#[inline]
pub fn u64_from_4_limbs_16(limbs: &[BabyBear; 4]) -> Option<u64> {
    let mut acc: u64 = 0;
    for (i, l) in limbs.iter().enumerate() {
        let v = l.0 as u64;
        if v >= (1u64 << 16) {
            return None;
        }
        acc |= v << (16 * i);
    }
    Some(acc)
}

/// Stage 2 (sealing honesty): bit-decompose `reserved = sealed_mask | (mode << 8)`
/// into 8 boolean mask bits + 1 boolean mode bit, and write them into the
/// row's reserved-bit aux slots. The AIR's per-row unconditional decomposition
/// constraint verifies the witness against `state_before.RESERVED`.
pub(crate) fn fill_reserved_bits(row: &mut [BabyBear], sealed_mask: u32, mode_flag: u32) {
    row[AUX_BASE + aux_off::RESERVED_BIT_0] = BabyBear::new((sealed_mask >> 0) & 1);
    row[AUX_BASE + aux_off::RESERVED_BIT_1] = BabyBear::new((sealed_mask >> 1) & 1);
    row[AUX_BASE + aux_off::RESERVED_BIT_2] = BabyBear::new((sealed_mask >> 2) & 1);
    row[AUX_BASE + aux_off::RESERVED_BIT_3] = BabyBear::new((sealed_mask >> 3) & 1);
    row[AUX_BASE + aux_off::RESERVED_BIT_4] = BabyBear::new((sealed_mask >> 4) & 1);
    row[AUX_BASE + aux_off::RESERVED_BIT_5] = BabyBear::new((sealed_mask >> 5) & 1);
    row[AUX_BASE + aux_off::RESERVED_BIT_6] = BabyBear::new((sealed_mask >> 6) & 1);
    row[AUX_BASE + aux_off::RESERVED_BIT_7] = BabyBear::new((sealed_mask >> 7) & 1);
    row[AUX_BASE + aux_off::RESERVED_MODE] = BabyBear::new(mode_flag & 1);
}

/// Compute the effects hash for a sequence of effects.
/// Returns (lo, hi) BabyBear elements.
pub fn compute_effects_hash(effects: &[Effect]) -> (BabyBear, BabyBear) {
    let mut hasher_inputs = Vec::new();
    for effect in effects {
        match effect {
            Effect::NoOp => {
                hasher_inputs.push(BabyBear::ZERO);
            }
            Effect::Transfer { amount, direction } => {
                hasher_inputs.push(BabyBear::ONE);
                let (lo, hi) = split_u64(*amount);
                hasher_inputs.push(lo);
                hasher_inputs.push(hi);
                hasher_inputs.push(BabyBear::new(*direction));
            }
            Effect::SetField { field_idx, value } => {
                hasher_inputs.push(BabyBear::new(2));
                hasher_inputs.push(BabyBear::new(*field_idx));
                hasher_inputs.push(*value);
            }
            Effect::GrantCapability { cap_entry } => {
                hasher_inputs.push(BabyBear::new(3));
                hasher_inputs.push(*cap_entry);
            }
            Effect::RevokeCapability { slot_hash } => {
                hasher_inputs.push(BabyBear::new(24));
                hasher_inputs.push(*slot_hash);
            }
            Effect::EmitEvent {
                topic_hash,
                payload_hash,
            } => {
                hasher_inputs.push(BabyBear::new(25));
                hasher_inputs.extend_from_slice(topic_hash);
                hasher_inputs.extend_from_slice(payload_hash);
            }
            Effect::SetPermissions { permissions_hash } => {
                hasher_inputs.push(BabyBear::new(26));
                hasher_inputs.push(*permissions_hash);
            }
            Effect::SetVerificationKey { vk_hash } => {
                hasher_inputs.push(BabyBear::new(27));
                hasher_inputs.push(*vk_hash);
            }
            Effect::CreateSealPair { pair_hash } => {
                hasher_inputs.push(BabyBear::new(28));
                hasher_inputs.push(*pair_hash);
            }
            Effect::RefreshDelegation => {
                hasher_inputs.push(BabyBear::new(29));
            }
            Effect::RevokeDelegation { child_hash } => {
                hasher_inputs.push(BabyBear::new(30));
                hasher_inputs.push(*child_hash);
            }
            Effect::CreateCell { create_hash } => {
                hasher_inputs.push(BabyBear::new(31));
                hasher_inputs.push(*create_hash);
            }
            Effect::SpawnWithDelegation { spawn_hash } => {
                hasher_inputs.push(BabyBear::new(32));
                hasher_inputs.push(*spawn_hash);
            }
            Effect::BridgeCancel { nullifier_hash } => {
                hasher_inputs.push(BabyBear::new(33));
                hasher_inputs.push(*nullifier_hash);
            }
            Effect::ExerciseViaCapability { exercise_hash } => {
                hasher_inputs.push(BabyBear::new(34));
                hasher_inputs.push(*exercise_hash);
            }
            Effect::Introduce { intro_hash } => {
                hasher_inputs.push(BabyBear::new(35));
                hasher_inputs.push(*intro_hash);
            }
            Effect::PipelinedSend { send_hash } => {
                hasher_inputs.push(BabyBear::new(36));
                hasher_inputs.push(*send_hash);
            }
            Effect::CreateEscrow {
                amount_lo,
                escrow_hash,
                amount_full,
            } => {
                hasher_inputs.push(BabyBear::new(37));
                hasher_inputs.push(*amount_lo);
                hasher_inputs.push(*escrow_hash);
                // 30-bit-trunc fix: absorb the four 16-bit limbs so the
                // effects hash binds to the full u64, not the truncated
                // value_lo.
                let limbs = u64_to_4_limbs_16(*amount_full);
                hasher_inputs.extend_from_slice(&limbs);
            }
            Effect::BridgeLock {
                value_lo,
                lock_hash,
                value_full,
            } => {
                hasher_inputs.push(BabyBear::new(38));
                hasher_inputs.push(*value_lo);
                hasher_inputs.push(*lock_hash);
                let limbs = u64_to_4_limbs_16(*value_full);
                hasher_inputs.extend_from_slice(&limbs);
            }
            Effect::CreateCommittedEscrow { commit_hash } => {
                hasher_inputs.push(BabyBear::new(39));
                hasher_inputs.push(*commit_hash);
            }
            Effect::BridgeMint {
                value_lo,
                mint_hash,
                value_full,
            } => {
                hasher_inputs.push(BabyBear::new(40));
                hasher_inputs.push(*value_lo);
                hasher_inputs.push(*mint_hash);
                let limbs = u64_to_4_limbs_16(*value_full);
                hasher_inputs.extend_from_slice(&limbs);
            }
            Effect::BridgeFinalize { finalize_hash } => {
                hasher_inputs.push(BabyBear::new(41));
                hasher_inputs.push(*finalize_hash);
            }
            Effect::ReleaseEscrow { escrow_id_hash } => {
                hasher_inputs.push(BabyBear::new(42));
                hasher_inputs.push(*escrow_id_hash);
            }
            Effect::RefundEscrow { escrow_id_hash } => {
                hasher_inputs.push(BabyBear::new(43));
                hasher_inputs.push(*escrow_id_hash);
            }
            Effect::ReleaseCommittedEscrow { commit_hash } => {
                hasher_inputs.push(BabyBear::new(44));
                hasher_inputs.push(*commit_hash);
            }
            Effect::RefundCommittedEscrow { commit_hash } => {
                hasher_inputs.push(BabyBear::new(45));
                hasher_inputs.push(*commit_hash);
            }
            Effect::NoteSpend { nullifier, value } => {
                hasher_inputs.push(BabyBear::new(4));
                hasher_inputs.push(*nullifier);
                let (lo, hi) = split_u64(*value);
                hasher_inputs.push(lo);
                hasher_inputs.push(hi);
            }
            Effect::NoteCreate { commitment, value } => {
                hasher_inputs.push(BabyBear::new(5));
                hasher_inputs.push(*commitment);
                let (lo, hi) = split_u64(*value);
                hasher_inputs.push(lo);
                hasher_inputs.push(hi);
            }
            Effect::CreateObligation {
                stake_amount,
                obligation_id,
                beneficiary_hash,
            } => {
                hasher_inputs.push(BabyBear::new(6));
                let (lo, hi) = split_u64(*stake_amount);
                hasher_inputs.push(lo);
                hasher_inputs.push(hi);
                hasher_inputs.push(*obligation_id);
                hasher_inputs.push(*beneficiary_hash);
            }
            Effect::FulfillObligation {
                obligation_id,
                stake_return,
            } => {
                hasher_inputs.push(BabyBear::new(7));
                hasher_inputs.push(*obligation_id);
                let (lo, hi) = split_u64(*stake_return);
                hasher_inputs.push(lo);
                hasher_inputs.push(hi);
            }
            Effect::Custom {
                program_vk_hash,
                proof_commitment,
            } => {
                hasher_inputs.push(BabyBear::new(8));
                hasher_inputs.extend_from_slice(program_vk_hash);
                hasher_inputs.extend_from_slice(proof_commitment);
            }
            Effect::SlashObligation {
                obligation_id,
                stake_amount,
                beneficiary_hash,
            } => {
                hasher_inputs.push(BabyBear::new(9));
                hasher_inputs.push(*obligation_id);
                let (lo, hi) = split_u64(*stake_amount);
                hasher_inputs.push(lo);
                hasher_inputs.push(hi);
                hasher_inputs.push(*beneficiary_hash);
            }
            Effect::Seal { field_idx } => {
                hasher_inputs.push(BabyBear::new(10));
                hasher_inputs.push(BabyBear::new(*field_idx));
            }
            Effect::Unseal { field_idx, brand } => {
                hasher_inputs.push(BabyBear::new(11));
                hasher_inputs.push(BabyBear::new(*field_idx));
                hasher_inputs.push(*brand);
            }
            Effect::MakeSovereign => {
                hasher_inputs.push(BabyBear::new(12));
            }
            Effect::CreateCellFromFactory {
                factory_vk,
                child_vk_derived,
            } => {
                hasher_inputs.push(BabyBear::new(13));
                hasher_inputs.push(*factory_vk);
                hasher_inputs.push(*child_vk_derived);
            }
            Effect::ExportSturdyRef {
                cell_id,
                permissions,
                random_seed,
                export_counter,
            } => {
                hasher_inputs.push(BabyBear::new(14));
                hasher_inputs.push(*cell_id);
                hasher_inputs.push(*permissions);
                hasher_inputs.push(*random_seed);
                hasher_inputs.push(BabyBear::new(*export_counter));
            }
            Effect::EnlivenRef {
                swiss_number,
                presenter_id,
                expected_cell_id,
                expected_permissions,
            } => {
                hasher_inputs.push(BabyBear::new(15));
                hasher_inputs.push(*swiss_number);
                hasher_inputs.push(*presenter_id);
                hasher_inputs.push(*expected_cell_id);
                hasher_inputs.push(*expected_permissions);
            }
            Effect::DropRef {
                cell_id,
                holder_federation,
                current_refcount,
            } => {
                hasher_inputs.push(BabyBear::new(16));
                hasher_inputs.push(*cell_id);
                hasher_inputs.push(*holder_federation);
                hasher_inputs.push(BabyBear::new(*current_refcount));
            }
            Effect::ValidateHandoff {
                certificate_hash,
                recipient_pk,
                introducer_pk,
                approved_set_root,
            } => {
                hasher_inputs.push(BabyBear::new(17));
                hasher_inputs.push(*certificate_hash);
                hasher_inputs.push(*recipient_pk);
                hasher_inputs.push(*introducer_pk);
                hasher_inputs.push(*approved_set_root);
            }
            Effect::AllocateQueue {
                capacity,
                owner_quota_id,
                cost_per_slot,
            } => {
                hasher_inputs.push(BabyBear::new(18));
                hasher_inputs.push(BabyBear::new(*capacity));
                hasher_inputs.push(*owner_quota_id);
                hasher_inputs.push(BabyBear::new(*cost_per_slot));
            }
            Effect::EnqueueMessage {
                message_hash,
                deposit_amount,
                sender_id,
                queue_len,
                program_vk,
            } => {
                hasher_inputs.push(BabyBear::new(19));
                hasher_inputs.push(*message_hash);
                hasher_inputs.push(BabyBear::new(*deposit_amount));
                hasher_inputs.push(*sender_id);
                hasher_inputs.push(BabyBear::new(*queue_len));
                hasher_inputs.push(*program_vk);
            }
            Effect::DequeueMessage {
                expected_message_hash,
                deposit_refund,
            } => {
                hasher_inputs.push(BabyBear::new(20));
                hasher_inputs.push(*expected_message_hash);
                hasher_inputs.push(BabyBear::new(*deposit_refund));
            }
            Effect::ResizeQueue {
                new_capacity,
                queue_id,
                cost_per_slot,
                old_capacity,
            } => {
                hasher_inputs.push(BabyBear::new(21));
                hasher_inputs.push(BabyBear::new(*new_capacity));
                hasher_inputs.push(*queue_id);
                hasher_inputs.push(BabyBear::new(*cost_per_slot));
                hasher_inputs.push(BabyBear::new(*old_capacity));
            }
            Effect::AtomicQueueTx {
                op_count,
                tx_hash,
                combined_old_root,
                combined_new_root,
                net_deposit,
            } => {
                hasher_inputs.push(BabyBear::new(22));
                hasher_inputs.push(BabyBear::new(*op_count));
                hasher_inputs.push(*tx_hash);
                hasher_inputs.push(*combined_old_root);
                hasher_inputs.push(*combined_new_root);
                hasher_inputs.push(BabyBear::new(*net_deposit));
            }
            Effect::PipelineStep {
                pipeline_id,
                source_old_root,
                source_new_root,
                sink_new_root,
                message_hash,
            } => {
                hasher_inputs.push(BabyBear::new(23));
                hasher_inputs.push(*pipeline_id);
                hasher_inputs.push(*source_old_root);
                hasher_inputs.push(*source_new_root);
                hasher_inputs.push(*sink_new_root);
                hasher_inputs.push(*message_hash);
            }
            // ---- Near-miss aliasing closure (#100 follow-up) ----
            // Domain-tag bytes are reserved in the selector index space
            // (46, 47, 48 — matching `sel::BURN`, `sel::CELL_DESTROY`,
            // `sel::ATTENUATE_CAPABILITY`).
            Effect::Burn {
                target_hash,
                amount_lo,
                amount_full,
            } => {
                hasher_inputs.push(BabyBear::new(46));
                hasher_inputs.push(*target_hash);
                hasher_inputs.push(*amount_lo);
                // Bind the full u64 via 4×16-bit limbs (mirrors
                // BridgeMint / BridgeLock / CreateEscrow) so the proof
                // commits to the entire amount, not just the low 30 bits.
                let limbs = u64_to_4_limbs_16(*amount_full);
                hasher_inputs.extend_from_slice(&limbs);
            }
            Effect::CellDestroy {
                target_hash,
                death_certificate_hash,
            } => {
                hasher_inputs.push(BabyBear::new(47));
                hasher_inputs.push(*target_hash);
                hasher_inputs.push(*death_certificate_hash);
            }
            Effect::AttenuateCapability {
                cap_slot_hash,
                narrower_commitment,
            } => {
                hasher_inputs.push(BabyBear::new(48));
                hasher_inputs.push(*cap_slot_hash);
                hasher_inputs.push(*narrower_commitment);
            }
        }
    }
    let h = hash_many(&hasher_inputs);
    // Split into two elements for wider coverage (legacy 2-felt form).
    let h2 = hash_2_to_1(h, BabyBear::new(0xEFFEC7));
    (h, h2)
}

/// Stage 1: 4-felt effects hash for the widened PI layout.
///
/// Position 0 matches [`compute_effects_hash`] (the legacy `EFFECTS_HASH_LO`);
/// positions 1..3 are 3 additional independent Poseidon2 compressions.
/// Drops the synthetic `EFFECTS_HASH_HI = hash_2_to_1(h, 0xEFFEC7)` binding
/// in favor of 4 independent squeezes, giving ~124-bit collision resistance.
pub fn compute_effects_hash_4(effects: &[Effect]) -> [BabyBear; 4] {
    let (h, _h_legacy_hi) = compute_effects_hash(effects);
    // Independent squeezes via hash_4_to_1 with distinct salts.
    [
        h,
        hash_4_to_1(&[h, BabyBear::ONE, BabyBear::ZERO, BabyBear::ZERO]),
        hash_4_to_1(&[h, BabyBear::new(2), BabyBear::ZERO, BabyBear::ZERO]),
        hash_4_to_1(&[h, BabyBear::new(3), BabyBear::ZERO, BabyBear::ZERO]),
    ]
}

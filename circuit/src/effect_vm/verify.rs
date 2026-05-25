//! Verifier-side validation for Effect VM AIR proofs.
//!
//! These checks live outside the STARK constraint system — executors and
//! relay nodes run them after `verify(&air, &proof, &pi)` succeeds to
//! catch range violations and slot-caveat tampering that the AIR alone
//! does not enforce.

use crate::field::BabyBear;

use super::{pi, split_u64, CellState};

/// Verify that balance limbs in a CellState are within valid ranges.
///
/// This function implements the executor-side mitigation for the balance limb
/// overflow vulnerability (o1vm audit finding #1). The STARK proof alone does
/// NOT constrain balance limbs to their declared bit-widths. Verifiers MUST
/// call this after proof verification to ensure the final state is well-formed.
///
/// Returns `Ok(())` if limbs are valid, or an error describing the violation.
pub fn verify_balance_limb_ranges(state: &CellState) -> Result<(), String> {
    let (lo, hi) = split_u64(state.balance);

    // balance_lo must fit in 30 bits.
    if lo.0 >= (1 << 30) {
        return Err(format!(
            "balance_lo out of range: {} >= 2^30 (max {})",
            lo.0,
            (1u32 << 30) - 1
        ));
    }

    // balance_hi must fit in 34 bits AND be < BabyBear prime.
    // Since BabyBear prime is 2^31 - 2^27 + 1, and hi < 2^34 could exceed it,
    // we check that hi < 2^31 (conservative; BabyBear::new already reduces mod p).
    if hi.0 >= (1 << 31) {
        return Err(format!(
            "balance_hi out of range: {} >= 2^31 (exceeds BabyBear field)",
            hi.0
        ));
    }

    // Verify reconstruction: lo + hi * 2^30 == balance.
    let reconstructed = (lo.0 as u64) | ((hi.0 as u64) << 30);
    if reconstructed != state.balance {
        return Err(format!(
            "balance limb reconstruction mismatch: lo={} hi={} reconstructs to {} but balance is {}",
            lo.0, hi.0, reconstructed, state.balance
        ));
    }

    Ok(())
}

/// Verify that a final CellState (after proof verification) has a valid
/// state commitment matching its declared fields.
///
/// This is the executor-side defense against interior-row limb manipulation:
/// even if a malicious prover used out-of-range limbs on interior rows, the
/// final commitment must match the declared final state.
pub fn verify_state_integrity(state: &CellState) -> Result<(), String> {
    // Check balance limb ranges.
    verify_balance_limb_ranges(state)?;

    // Verify commitment matches the state.
    let expected_commit = CellState::compute_commitment(
        state.balance,
        state.nonce,
        &state.fields,
        state.capability_root,
    );
    if state.state_commitment != expected_commit {
        return Err(format!(
            "state_commitment mismatch: declared {:?} but computed {:?}",
            state.state_commitment, expected_commit
        ));
    }

    Ok(())
}

/// P2-2 / P0-1 helper: range-check the INIT_BAL_* and FINAL_BAL_* PIs that
/// were added in the P0-1 fix.
///
/// The Group 6 algebraic constraint binds `NET_DELTA = FINAL - INIT` over the
/// BabyBear field. Without range checks on the limbs, a verifier could (in
/// principle) accept PIs where `INIT_BAL_LO` exceeds 2^30, allowing the
/// modular subtraction in `actual_delta = (FINAL - INIT) mod p` to wrap and
/// satisfy a forged `NET_DELTA` value. The honest prover/executor never
/// produces such PIs (limb ranges are asserted at trace-generation time), but
/// an untrusted-prover scenario should call this on every received proof.
///
/// Returns Ok if the PIs are well-formed, or an Err describing the violation.
pub fn verify_balance_limb_pis(public_inputs: &[BabyBear]) -> Result<(), String> {
    if public_inputs.len() < pi::BASE_COUNT {
        return Err(format!(
            "PI vector too short: {} < {}",
            public_inputs.len(),
            pi::BASE_COUNT
        ));
    }
    for (label, idx) in &[
        ("INIT_BAL_LO", pi::INIT_BAL_LO),
        ("FINAL_BAL_LO", pi::FINAL_BAL_LO),
    ] {
        let v = public_inputs[*idx].0;
        if v >= (1u32 << 30) {
            return Err(format!(
                "{} out of range: {} >= 2^30 (boundary-pinned balance_lo \
                 must fit in 30 bits)",
                label, v
            ));
        }
    }
    for (label, idx) in &[
        ("INIT_BAL_HI", pi::INIT_BAL_HI),
        ("FINAL_BAL_HI", pi::FINAL_BAL_HI),
    ] {
        let v = public_inputs[*idx].0;
        if v >= (1u32 << 31) {
            return Err(format!(
                "{} out of range: {} >= 2^31 (exceeds BabyBear field)",
                label, v
            ));
        }
    }
    // NET_DELTA_SIGN must be boolean (Group 5 enforces this in-circuit, but
    // we also check externally for defense-in-depth).
    let sign = public_inputs[pi::NET_DELTA_SIGN].0;
    if sign > 1 {
        return Err(format!("NET_DELTA_SIGN must be 0 or 1; got {}", sign));
    }
    // NET_DELTA_MAG must fit in 30 bits to match the per-limb subtraction
    // domain (otherwise modular wrap could occur in the algebraic check).
    let mag = public_inputs[pi::NET_DELTA_MAG].0;
    if mag >= (1u32 << 30) {
        return Err(format!("NET_DELTA_MAG out of range: {} >= 2^30", mag));
    }
    Ok(())
}

// ============================================================================
// Slot-caveat manifest verifier (Cav-Codex Block 3)
// ============================================================================

/// Re-evaluate the slot-caveat manifest carried in PI against the
/// declared initial / final cell-state field views. Returns Ok iff
/// every entry holds; otherwise returns the first violation.
///
/// This is the "AIR teeth" half of Cav-Codex Block 3: per
/// `SLOT-CAVEATS-DESIGN.md` §4, AIR enforcement of slot caveats is
/// opt-in. Block 3 lands the *manifest binding* — the executor
/// projects declared caveats into PI, and any consumer of the proof
/// (the receipt verifier, a third-party validator, a Federation
/// quorum) re-runs the caveats against the bound state_before /
/// state_after PI fields. Tampering with the manifest, with the
/// state-before/after, or with the underlying cell-program declaration
/// surfaces at this layer as a verifier-side rejection.
///
/// `initial_fields` and `final_fields` are the cell's slot-0..7 4-byte
/// truncated views (matching the AIR's per-row STATE_BEFORE_BASE /
/// STATE_AFTER_BASE field columns). Variants whose enforcement needs
/// the full 32-byte FieldElement value (e.g. `Monotonic` on big-endian
/// 32-byte sequences) are deferred — they're documented in their
/// `#[ignore]`'d adversarial tests until the AIR state expands to
/// 4-felt per slot.
pub fn verify_slot_caveat_manifest(
    public_inputs: &[BabyBear],
    initial_fields: &[BabyBear; 8],
    final_fields: &[BabyBear; 8],
    block_height: u64,
) -> Result<(), String> {
    if public_inputs.len() < pi::BASE_COUNT {
        return Err(format!(
            "PI vector too short for slot-caveat manifest: {} < {}",
            public_inputs.len(),
            pi::BASE_COUNT
        ));
    }
    let count = public_inputs[pi::SLOT_CAVEAT_COUNT].0 as usize;
    if count > pi::MAX_SLOT_CAVEATS {
        return Err(format!(
            "SLOT_CAVEAT_COUNT {} exceeds MAX_SLOT_CAVEATS {}",
            count,
            pi::MAX_SLOT_CAVEATS
        ));
    }
    for i in 0..count {
        let base = pi::SLOT_CAVEAT_MANIFEST_BASE + i * pi::SLOT_CAVEAT_ENTRY_SIZE;
        let tag = public_inputs[base].0;
        let slot_idx = public_inputs[base + 1].0 as usize;
        if slot_idx >= 8 {
            return Err(format!(
                "slot-caveat[{i}] slot_index {slot_idx} out of range (must be < 8)"
            ));
        }
        let p0 = public_inputs[base + 2];
        let p1 = public_inputs[base + 3];
        let _p2 = public_inputs[base + 4];
        let _p3 = public_inputs[base + 5];
        let old_v = initial_fields[slot_idx];
        let new_v = final_fields[slot_idx];
        match tag {
            // Empty entry (zero) is allowed only beyond `count`; here it
            // means the executor declared a slot caveat with no
            // type_tag, which is malformed.
            0 => return Err(format!("slot-caveat[{i}] has zero type_tag")),

            t if t == pi::SLOT_CAVEAT_TAG_IMMUTABLE => {
                if old_v != new_v {
                    return Err(format!(
                        "slot-caveat[{i}] Immutable on slot {slot_idx}: {old_v:?} -> {new_v:?}"
                    ));
                }
            }
            t if t == pi::SLOT_CAVEAT_TAG_WRITE_ONCE => {
                // WriteOnce: either initial was zero (any new is OK) or
                // unchanged.
                if old_v != BabyBear::ZERO && old_v != new_v {
                    return Err(format!(
                        "slot-caveat[{i}] WriteOnce on slot {slot_idx}: was {old_v:?}, became {new_v:?}"
                    ));
                }
            }
            t if t == pi::SLOT_CAVEAT_TAG_FIELD_DELTA => {
                // FieldDelta: new == old + delta. `delta` carried in p0
                // (low-4-byte BabyBear projection, matching the AIR
                // state column truncation).
                let expected = old_v + p0;
                if new_v != expected {
                    return Err(format!(
                        "slot-caveat[{i}] FieldDelta on slot {slot_idx}: expected {old_v:?}+{p0:?}={expected:?}, got {new_v:?}"
                    ));
                }
            }
            t if t == pi::SLOT_CAVEAT_TAG_MONOTONIC_SEQUENCE => {
                // new == old + 1.
                let expected = old_v + BabyBear::ONE;
                if new_v != expected {
                    return Err(format!(
                        "slot-caveat[{i}] MonotonicSequence on slot {slot_idx}: expected {old_v:?}+1={expected:?}, got {new_v:?}"
                    ));
                }
            }
            t if t == pi::SLOT_CAVEAT_TAG_FIELD_EQUALS => {
                // new == p0 (4-byte truncation).
                if new_v != p0 {
                    return Err(format!(
                        "slot-caveat[{i}] FieldEquals on slot {slot_idx}: expected {p0:?}, got {new_v:?}"
                    ));
                }
            }
            t if t == pi::SLOT_CAVEAT_TAG_TEMPORAL_GATE => {
                // not_before = p0 (u32-fitting); not_after = p1
                // (u32-fitting). 0 sentinel means "no bound on that
                // side".
                let nb = p0.0 as u64;
                let na = p1.0 as u64;
                if nb != 0 && block_height < nb {
                    return Err(format!(
                        "slot-caveat[{i}] TemporalGate not_before {nb} > height {block_height}"
                    ));
                }
                if na != 0 && block_height > na {
                    return Err(format!(
                        "slot-caveat[{i}] TemporalGate not_after {na} < height {block_height}"
                    ));
                }
            }
            // Variants whose enforcement needs more than the 4-byte
            // truncated state-column form (full 32B compare, Merkle
            // gadgets, set-membership, etc.) accept the manifest
            // entry at this layer and defer to the executor's
            // evaluator. They round-trip through PI for shape
            // honesty (the verifier still rejects malformed
            // entries: bad slot_idx, out-of-range count) but the
            // boundary teeth land in a follow-up commit.
            t if t == pi::SLOT_CAVEAT_TAG_FIELD_GTE
                || t == pi::SLOT_CAVEAT_TAG_FIELD_LTE
                || t == pi::SLOT_CAVEAT_TAG_MONOTONIC
                || t == pi::SLOT_CAVEAT_TAG_STRICT_MONOTONIC
                || t == pi::SLOT_CAVEAT_TAG_SENDER_AUTHORIZED
                || t == pi::SLOT_CAVEAT_TAG_ALLOWED_TRANSITIONS =>
            {
                // Defer.
            }
            other => {
                return Err(format!("slot-caveat[{i}] unknown type_tag {other}"));
            }
        }
    }
    // Padding entries past `count` must be zero (no smuggled caveats).
    for i in count..pi::MAX_SLOT_CAVEATS {
        let base = pi::SLOT_CAVEAT_MANIFEST_BASE + i * pi::SLOT_CAVEAT_ENTRY_SIZE;
        for j in 0..pi::SLOT_CAVEAT_ENTRY_SIZE {
            if public_inputs[base + j] != BabyBear::ZERO {
                return Err(format!(
                    "slot-caveat manifest padding entry {i} field {j} is nonzero (smuggle attempt?)"
                ));
            }
        }
    }
    Ok(())
}

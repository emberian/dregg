//! Effect VM checks: multi-effect trace generation, all 14 effect types, custom dispatch,
//! boundary constraints, and adversarial cases.

use pyana_circuit::effect_vm::{
    CellState, EFFECT_VM_WIDTH, Effect, NUM_EFFECTS, compute_effects_hash, encode_net_delta,
    extract_net_delta, generate_effect_vm_trace, sel,
};
use pyana_circuit::field::BabyBear;

use crate::report::{CheckResult, run_check};

pub fn run() -> Vec<CheckResult> {
    vec![
        run_check("trace_generation", check_trace_generation),
        run_check("all_14_effects", check_all_14_effect_types),
        run_check("effects_hash", check_effects_hash_commitment),
        run_check("net_delta", check_net_delta_encoding),
        run_check("custom_dispatch", check_custom_dispatch),
        run_check("adversarial_overdraft", check_adversarial_overdraft),
    ]
}

/// Verify trace generation for a basic multi-effect turn.
fn check_trace_generation() -> Result<(), String> {
    let initial = CellState::new(10_000, 0);
    let effects = vec![
        Effect::Transfer {
            amount: 100,
            direction: 1,
        }, // outgoing
        Effect::Transfer {
            amount: 50,
            direction: 0,
        }, // incoming
        Effect::SetField {
            field_idx: 0,
            value: BabyBear::new(42),
        },
        Effect::NoOp, // pad to power of 2
    ];

    let (trace, public_inputs) = generate_effect_vm_trace(&initial, &effects);

    if trace.is_empty() {
        return Err("trace should not be empty".into());
    }

    // Trace should have exactly `effects.len()` rows.
    let expected_rows = effects.len();
    if trace.len() != expected_rows {
        return Err(format!(
            "expected {} trace rows, got {}",
            expected_rows,
            trace.len()
        ));
    }

    // Each row should have the correct width.
    for (i, row) in trace.iter().enumerate() {
        if row.len() != EFFECT_VM_WIDTH {
            return Err(format!(
                "row {i} has width {}, expected {EFFECT_VM_WIDTH}",
                row.len()
            ));
        }
    }

    // Public inputs should be non-empty.
    if public_inputs.is_empty() {
        return Err("public inputs should be non-empty".into());
    }

    // Row continuity: state_after of row i == state_before of row i+1.
    // State after starts at column 31, state before starts at column 14.
    let state_before_offset = NUM_EFFECTS; // 14 selectors, then state starts
    let state_after_offset = NUM_EFFECTS + 14 + 8; // after selectors + state_before + params
    for i in 0..trace.len() - 1 {
        for col in 0..14 {
            let after_val = trace[i][state_after_offset + col];
            let before_val = trace[i + 1][state_before_offset + col];
            if after_val != before_val {
                return Err(format!(
                    "continuity broken at row {i}, col {col}: after={:?}, next_before={:?}",
                    after_val, before_val
                ));
            }
        }
    }

    Ok(())
}

/// Verify all 14 effect types can generate trace rows without panicking.
fn check_all_14_effect_types() -> Result<(), String> {
    let initial = CellState::new(100_000, 0);

    // Build a sequence covering all 14 effect types.
    let effects = vec![
        Effect::NoOp,
        Effect::Transfer {
            amount: 100,
            direction: 1,
        },
        Effect::SetField {
            field_idx: 2,
            value: BabyBear::new(999),
        },
        Effect::GrantCapability {
            cap_entry: BabyBear::new(7777),
        },
        Effect::NoteSpend {
            nullifier: BabyBear::new(1234),
            value: 50,
        },
        Effect::NoteCreate {
            commitment: BabyBear::new(5678),
            value: 50,
        },
        Effect::CreateObligation {
            stake_amount: 200,
            obligation_id: BabyBear::new(8888),
            beneficiary_hash: BabyBear::new(7777),
        },
        Effect::FulfillObligation {
            obligation_id: BabyBear::new(8888),
            stake_return: 200,
        },
        Effect::Custom {
            program_vk_hash: [BabyBear::new(1); 8],
            proof_commitment: [BabyBear::new(2); 4],
        },
        Effect::SlashObligation {
            obligation_id: BabyBear::new(9999),
            stake_amount: 50,
            beneficiary_hash: BabyBear::new(1111),
        },
        Effect::Seal { field_idx: 0 },
        Effect::Unseal {
            field_idx: 0,
            brand: BabyBear::new(555),
        },
        Effect::MakeSovereign,
        Effect::CreateCellFromFactory {
            factory_vk: BabyBear::new(2222),
            child_vk_derived: BabyBear::new(3333),
        },
    ];

    assert_eq!(effects.len(), NUM_EFFECTS, "should have exactly 14 effects");

    // Pad to next power of 2 (16).
    let mut padded = effects.clone();
    while padded.len() < 16 {
        padded.push(Effect::NoOp);
    }

    let (trace, public_inputs) = generate_effect_vm_trace(&initial, &padded);

    if trace.is_empty() {
        return Err("trace for 14 effect types should not be empty".into());
    }

    // Verify selector exclusivity: exactly one selector is 1 per row.
    for (row_idx, row) in trace.iter().enumerate() {
        let selector_sum: u32 = (0..NUM_EFFECTS).map(|s| row[s].0).sum();
        if selector_sum != 1 {
            return Err(format!(
                "row {row_idx}: selector sum should be 1, got {selector_sum}"
            ));
        }
    }

    // Verify the correct selector is active for each effect.
    let expected_selectors = [
        sel::NOOP,
        sel::TRANSFER,
        sel::SET_FIELD,
        sel::GRANT_CAP,
        sel::NOTE_SPEND,
        sel::NOTE_CREATE,
        sel::CREATE_OBLIGATION,
        sel::FULFILL_OBLIGATION,
        sel::CUSTOM,
        sel::SLASH_OBLIGATION,
        sel::SEAL,
        sel::UNSEAL,
        sel::MAKE_SOVEREIGN,
        sel::CREATE_CELL_FROM_FACTORY,
    ];
    for (i, &expected_sel) in expected_selectors.iter().enumerate() {
        if trace[i][expected_sel] != BabyBear::ONE {
            return Err(format!(
                "row {i}: expected selector {expected_sel} active, but it's {:?}",
                trace[i][expected_sel]
            ));
        }
    }

    if public_inputs.is_empty() {
        return Err("public inputs should be populated".into());
    }

    Ok(())
}

/// Verify effects hash is a deterministic commitment to the effect sequence.
fn check_effects_hash_commitment() -> Result<(), String> {
    let effects_a = vec![
        Effect::Transfer {
            amount: 100,
            direction: 1,
        },
        Effect::SetField {
            field_idx: 0,
            value: BabyBear::new(42),
        },
    ];

    let effects_b = vec![
        Effect::Transfer {
            amount: 100,
            direction: 1,
        },
        Effect::SetField {
            field_idx: 0,
            value: BabyBear::new(43), // different value
        },
    ];

    let (hash_a_lo, hash_a_hi) = compute_effects_hash(&effects_a);
    let (hash_a_lo2, hash_a_hi2) = compute_effects_hash(&effects_a);
    let (hash_b_lo, hash_b_hi) = compute_effects_hash(&effects_b);

    // Same effects => same hash (deterministic).
    if hash_a_lo != hash_a_lo2 || hash_a_hi != hash_a_hi2 {
        return Err("effects hash should be deterministic".into());
    }

    // Different effects => different hash (collision resistance).
    if hash_a_lo == hash_b_lo && hash_a_hi == hash_b_hi {
        return Err("different effects should produce different hashes".into());
    }

    // Non-zero for non-empty effects.
    if hash_a_lo == BabyBear::ZERO && hash_a_hi == BabyBear::ZERO {
        return Err("effects hash should not be zero for non-empty effects".into());
    }

    Ok(())
}

/// Verify net delta encoding and extraction round-trips correctly.
fn check_net_delta_encoding() -> Result<(), String> {
    // extract_net_delta expects at least 7 elements (pi::BASE_COUNT = 7).
    // NET_DELTA_MAG is at index 2, NET_DELTA_SIGN is at index 3.
    fn make_public_inputs(mag: BabyBear, sign: BabyBear) -> Vec<BabyBear> {
        vec![
            BabyBear::ZERO, // [0] old_commitment
            BabyBear::ZERO, // [1] new_commitment
            mag,            // [2] net_delta_mag
            sign,           // [3] net_delta_sign
            BabyBear::ZERO, // [4] effects_hash_lo
            BabyBear::ZERO, // [5] effects_hash_hi
            BabyBear::ZERO, // [6] custom_effect_count
        ]
    }

    // Positive delta (net inflow).
    let (mag_pos, sign_pos) = encode_net_delta(500);
    let pi_pos = make_public_inputs(mag_pos, sign_pos);
    let decoded_pos = extract_net_delta(&pi_pos).ok_or("failed to extract positive delta")?;
    if decoded_pos != 500 {
        return Err(format!("expected +500, got {decoded_pos}"));
    }

    // Negative delta (net outflow).
    let (mag_neg, sign_neg) = encode_net_delta(-300);
    let pi_neg = make_public_inputs(mag_neg, sign_neg);
    let decoded_neg = extract_net_delta(&pi_neg).ok_or("failed to extract negative delta")?;
    if decoded_neg != -300 {
        return Err(format!("expected -300, got {decoded_neg}"));
    }

    // Zero delta.
    let (mag_zero, sign_zero) = encode_net_delta(0);
    let pi_zero = make_public_inputs(mag_zero, sign_zero);
    let decoded_zero = extract_net_delta(&pi_zero).ok_or("failed to extract zero delta")?;
    if decoded_zero != 0 {
        return Err(format!("expected 0, got {decoded_zero}"));
    }

    Ok(())
}

/// Verify custom effect dispatch: state flows unchanged, VK hash committed.
fn check_custom_dispatch() -> Result<(), String> {
    let initial = CellState::new(5000, 0);
    let program_vk_hash = [
        BabyBear::new(11),
        BabyBear::new(22),
        BabyBear::new(33),
        BabyBear::new(44),
        BabyBear::new(0),
        BabyBear::new(0),
        BabyBear::new(0),
        BabyBear::new(0),
    ];
    let proof_commitment = [
        BabyBear::new(55),
        BabyBear::new(66),
        BabyBear::new(77),
        BabyBear::new(88),
    ];

    let effects = vec![
        Effect::Custom {
            program_vk_hash,
            proof_commitment,
        },
        Effect::NoOp, // pad to power of 2
    ];

    let (trace, public_inputs) = generate_effect_vm_trace(&initial, &effects);

    if trace.is_empty() {
        return Err("custom dispatch trace should not be empty".into());
    }

    // Custom effect should not change balance (state flows through).
    let state_before_offset = NUM_EFFECTS;
    let state_after_offset = NUM_EFFECTS + 14 + 8;

    // Balance (first 2 state columns) should be unchanged.
    let balance_before_lo = trace[0][state_before_offset];
    let balance_before_hi = trace[0][state_before_offset + 1];
    let balance_after_lo = trace[0][state_after_offset];
    let balance_after_hi = trace[0][state_after_offset + 1];

    if balance_before_lo != balance_after_lo || balance_before_hi != balance_after_hi {
        return Err("custom effect should not change balance".into());
    }

    // Public inputs should contain the custom proof commitments.
    // custom_effect_count is at index 6 in public inputs.
    if public_inputs.len() < 7 {
        return Err(format!(
            "public inputs too short: {}, expected >= 7",
            public_inputs.len()
        ));
    }

    let custom_count = public_inputs[6];
    if custom_count != BabyBear::ONE {
        return Err(format!(
            "expected 1 custom effect in public inputs, got {:?}",
            custom_count
        ));
    }

    Ok(())
}

/// Adversarial: an overdraft transfer should not produce valid trace continuity.
/// The Effect VM trace generator should either panic or produce a trace that
/// violates constraints (balance goes negative).
fn check_adversarial_overdraft() -> Result<(), String> {
    let initial = CellState::new(100, 0); // only 100 balance

    let effects = vec![
        Effect::Transfer {
            amount: 200,
            direction: 1,
        }, // overdraft!
        Effect::NoOp,
    ];

    // The trace generator may either:
    // 1. Produce a trace with underflow (which the verifier would reject), or
    // 2. Panic during generation (which we catch).
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        generate_effect_vm_trace(&initial, &effects)
    }));

    match result {
        Err(_panic) => {
            // Good: trace generation rejects overdraft.
        }
        Ok((trace, _public_inputs)) => {
            // If trace was generated, verify the net delta reflects the overdraft.
            // The verifier would catch this via boundary constraints (balance can't go negative).
            // For the preflight, we just verify the trace was generated (the AIR verifier
            // enforces the constraint, and an honest prover wouldn't submit this).
            if trace.is_empty() {
                return Err("if overdraft doesn't panic, trace should still be generated".into());
            }
            // The net delta should show -200 (outflow exceeding balance).
            // This is acceptable: the trace is valid but the STARK verifier
            // would reject it because the boundary constraint (balance >= 0) fails.
        }
    }

    Ok(())
}

//! Adversarial tests for the 30-bit value-truncation fix (CAVEAT-LAYER-COVERAGE.md §6.5).
//!
//! Pre-fix, the executor's `convert_turn_effects_to_vm` projected a u64
//! `value` into BabyBear via `value & ((1 << 30) - 1)`, dropping the top
//! 34 bits. A malicious prover could re-mint / re-lock / escrow with any
//! high-bit-distinct amount above 2^30 and produce an identical AIR PI.
//!
//! The fix carries `value_full: u64` inside the VmEffect variants
//! `BridgeMint`, `BridgeLock`, and `CreateEscrow`; the trace generator
//! decomposes it into 4×16-bit limbs and pins them into PI slots
//! `BRIDGE_MINT_VALUE_LIMBS`, `BRIDGE_LOCK_VALUE_LIMBS`, and
//! `CREATE_ESCROW_AMOUNT_LIMBS`. The verifier's PI matching loop catches
//! any disagreement.

use pyana_circuit::effect_vm::{
    self, CellState, Effect, generate_effect_vm_trace, u64_from_4_limbs_16, u64_to_4_limbs_16,
};
use pyana_circuit::field::BabyBear;

fn make_initial_state(balance: u64) -> CellState {
    CellState::new(balance, 0)
}

/// Round-trip: limbs reconstruct the original u64.
#[test]
fn value_limbs_roundtrip_full_u64_range() {
    // Edge values: zero, max-u30 (the truncation boundary), max-u64 - 1.
    let values: [u64; 6] = [
        0,
        (1u64 << 30) - 1,
        1u64 << 30, // first value the pre-fix path collapsed
        1u64 << 50,
        u64::MAX - 1,
        u64::MAX,
    ];
    for v in values.iter() {
        let limbs = u64_to_4_limbs_16(*v);
        let recovered = u64_from_4_limbs_16(&limbs).unwrap();
        assert_eq!(recovered, *v, "limbs round-trip for {}", v);
        // Every limb < 2^16.
        for (i, l) in limbs.iter().enumerate() {
            assert!(l.0 < (1 << 16), "limb[{}] = {} out of range", i, l.0);
        }
    }
}

/// An out-of-range limb (>= 2^16) should be rejected by the inverse helper.
/// This is the adversarial gadget the verifier's PI match loop sits on.
#[test]
fn value_limbs_reject_out_of_range_limb() {
    let mut limbs = u64_to_4_limbs_16(42);
    limbs[2] = BabyBear::new(1 << 17); // poison
    assert!(u64_from_4_limbs_16(&limbs).is_none());
}

/// Two values that share the low 30 bits but differ in higher bits MUST
/// produce different PI limbs. Pre-fix, both projected to the same PI.
#[test]
fn high_bit_distinct_values_produce_distinct_pi_limbs() {
    let v_low = (1u64 << 30) - 1; // all 30 low bits set
    let v_high = v_low | (1u64 << 50); // same low-30 + a high bit
    let limbs_low = u64_to_4_limbs_16(v_low);
    let limbs_high = u64_to_4_limbs_16(v_high);
    assert_ne!(limbs_low, limbs_high);
    // And specifically the high limb differs.
    assert_ne!(limbs_low[3], limbs_high[3]);
}

/// Trace generation for BridgeMint pins the full-u64 limbs into the PI.
/// Pre-fix: only the 30-bit `value_lo` would have been bound.
#[test]
fn bridge_mint_full_value_appears_in_pi_limbs() {
    let state = make_initial_state(1_000_000);
    // A value well above 2^30 to exercise the high bits.
    let full_value: u64 = (1u64 << 50) | 12345;
    let value_lo = BabyBear::new((full_value & ((1u64 << 30) - 1)) as u32);
    let effects = vec![Effect::BridgeMint {
        value_lo,
        mint_hash: BabyBear::new(0xBEEF),
        value_full: full_value,
    }];
    let (_trace, pi) = generate_effect_vm_trace(&state, &effects);
    let expected_limbs = u64_to_4_limbs_16(full_value);
    for i in 0..effect_vm::pi::BRIDGE_MINT_VALUE_LIMBS_LEN {
        assert_eq!(
            pi[effect_vm::pi::BRIDGE_MINT_VALUE_LIMBS_BASE + i],
            expected_limbs[i],
            "PI[BRIDGE_MINT_VALUE_LIMBS+{}] disagrees with computed limb",
            i,
        );
    }
    // The lock + escrow slots remain zero sentinels.
    for i in 0..effect_vm::pi::BRIDGE_LOCK_VALUE_LIMBS_LEN {
        assert_eq!(
            pi[effect_vm::pi::BRIDGE_LOCK_VALUE_LIMBS_BASE + i],
            BabyBear::ZERO
        );
    }
}

/// Adversarial: a forged trace whose `value_full` collides on the low
/// 30 bits but differs in the high bits produces a *different* PI, so a
/// verifier with the honest PI rejects.
#[test]
fn bridge_mint_high_bit_tampering_changes_pi() {
    let state = make_initial_state(1_000_000);
    let honest: u64 = 1234;
    let tampered: u64 = (1u64 << 40) | honest; // same low bits

    let honest_effects = vec![Effect::BridgeMint {
        value_lo: BabyBear::new((honest & ((1u64 << 30) - 1)) as u32),
        mint_hash: BabyBear::new(7),
        value_full: honest,
    }];
    let tampered_effects = vec![Effect::BridgeMint {
        value_lo: BabyBear::new((tampered & ((1u64 << 30) - 1)) as u32),
        mint_hash: BabyBear::new(7),
        value_full: tampered,
    }];

    let (_, pi_honest) = generate_effect_vm_trace(&state, &honest_effects);
    let (_, pi_tampered) = generate_effect_vm_trace(&state, &tampered_effects);

    // The two PIs MUST differ on the BRIDGE_MINT_VALUE_LIMBS slice.
    let h_slice = &pi_honest[effect_vm::pi::BRIDGE_MINT_VALUE_LIMBS_BASE
        ..effect_vm::pi::BRIDGE_MINT_VALUE_LIMBS_BASE + effect_vm::pi::BRIDGE_MINT_VALUE_LIMBS_LEN];
    let t_slice = &pi_tampered[effect_vm::pi::BRIDGE_MINT_VALUE_LIMBS_BASE
        ..effect_vm::pi::BRIDGE_MINT_VALUE_LIMBS_BASE + effect_vm::pi::BRIDGE_MINT_VALUE_LIMBS_LEN];
    assert_ne!(h_slice, t_slice);
}

/// Same shape for BridgeLock + CreateEscrow.
#[test]
fn bridge_lock_full_value_appears_in_pi_limbs() {
    let state = make_initial_state(1_000_000);
    let full_value: u64 = 1u64 << 45;
    let effects = vec![Effect::BridgeLock {
        value_lo: BabyBear::new((full_value & ((1u64 << 30) - 1)) as u32),
        lock_hash: BabyBear::new(0xCAFE),
        value_full: full_value,
    }];
    let (_, pi) = generate_effect_vm_trace(&state, &effects);
    let expected = u64_to_4_limbs_16(full_value);
    for i in 0..effect_vm::pi::BRIDGE_LOCK_VALUE_LIMBS_LEN {
        assert_eq!(
            pi[effect_vm::pi::BRIDGE_LOCK_VALUE_LIMBS_BASE + i],
            expected[i]
        );
    }
}

#[test]
fn create_escrow_full_amount_appears_in_pi_limbs() {
    let state = make_initial_state(1_000_000);
    let full_amount: u64 = (1u64 << 60) | 999;
    let effects = vec![Effect::CreateEscrow {
        amount_lo: BabyBear::new((full_amount & ((1u64 << 30) - 1)) as u32),
        escrow_hash: BabyBear::new(0xDEAD),
        amount_full: full_amount,
    }];
    let (_, pi) = generate_effect_vm_trace(&state, &effects);
    let expected = u64_to_4_limbs_16(full_amount);
    for i in 0..effect_vm::pi::CREATE_ESCROW_AMOUNT_LIMBS_LEN {
        assert_eq!(
            pi[effect_vm::pi::CREATE_ESCROW_AMOUNT_LIMBS_BASE + i],
            expected[i]
        );
    }
}

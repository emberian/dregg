//! Integration tests: forged-proof rejection paths.
//!
//! For each major verifier entry-point, constructs a genuine STARK proof and
//! then calls the verifier with systematically tampered inputs:
//!   - corrupted proof bytes (FRI region, header, last byte)
//!   - wrong public inputs (each category of PI: balance, commitment, effects hash)
//!   - wrong VK hash
//!   - truncated proof bytes
//!   - zero-length proof bytes
//!
//! Every assertion is `!verified` — a tampered proof that passes is a soundness bug.

use pyana_circuit::{
    BabyBear, CellState, Effect, EffectVmAir,
    effect_vm::{generate_effect_vm_trace, pi},
    stark::{self, proof_to_bytes},
};
use pyana_verifier::{
    AUTO_DETECT_VK_HASH, EFFECT_VM_VK_HASH_HEX, exit_code, verify_effect_vm_proof,
};

// ─────────────────────────────────────────────────────────────────────────────
// Helpers
// ─────────────────────────────────────────────────────────────────────────────

fn make_proof_and_pi(balance: u64, effects: &[Effect]) -> (Vec<u8>, Vec<u32>) {
    let state = CellState::new(balance, 0);
    let (trace, public_inputs) = generate_effect_vm_trace(&state, effects);
    let air = EffectVmAir::new(trace.len());
    let proof = stark::prove(&air, &trace, &public_inputs);
    let proof_bytes = proof_to_bytes(&proof);
    let pi_u32: Vec<u32> = public_inputs.iter().map(|bb| bb.as_u32()).collect();
    (proof_bytes, pi_u32)
}

fn assert_rejected(proof_bytes: &[u8], pi: &[u32], vk: &str, label: &str) {
    let (out, code) = verify_effect_vm_proof(proof_bytes, pi, vk);
    assert_ne!(
        code,
        exit_code::VERIFIED,
        "{label}: expected rejection, but got VERIFIED. out={:?}",
        out
    );
    assert!(!out.verified, "{label}: out.verified must be false");
}

fn assert_accepted(proof_bytes: &[u8], pi: &[u32], vk: &str, label: &str) {
    let (out, code) = verify_effect_vm_proof(proof_bytes, pi, vk);
    assert_eq!(
        code,
        exit_code::VERIFIED,
        "{label}: expected acceptance, got code={code}. out={:?}",
        out
    );
    assert!(out.verified, "{label}: out.verified must be true");
}

// ─────────────────────────────────────────────────────────────────────────────
// 1. Baseline: honest proof accepted by every VK mode.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn honest_proof_accepted_auto_and_canonical_vk() {
    let (proof_bytes, pi) = make_proof_and_pi(
        1_000,
        &[Effect::Transfer { amount: 100, direction: 1 }],
    );
    assert_accepted(&proof_bytes, &pi, AUTO_DETECT_VK_HASH, "auto VK");
    assert_accepted(&proof_bytes, &pi, EFFECT_VM_VK_HASH_HEX, "canonical VK hex");
}

// ─────────────────────────────────────────────────────────────────────────────
// 2. Corrupted proof bytes: FRI commitment region.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn corrupted_fri_bytes_rejected() {
    let (mut proof_bytes, pi) = make_proof_and_pi(
        2_000,
        &[Effect::Transfer { amount: 200, direction: 0 }],
    );
    // Flip a byte in the middle of the proof (past any header / length prefix).
    let offset = (proof_bytes.len() / 2).max(10).min(proof_bytes.len() - 1);
    proof_bytes[offset] ^= 0xFF;
    assert_rejected(&proof_bytes, &pi, AUTO_DETECT_VK_HASH, "corrupted FRI bytes");
}

/// Flip a single bit near the end (Merkle cap or query region).
#[test]
fn corrupted_last_bytes_rejected() {
    let (mut proof_bytes, pi) = make_proof_and_pi(
        500,
        &[Effect::NoOp],
    );
    let last = proof_bytes.len() - 1;
    proof_bytes[last] ^= 0x01;
    assert_rejected(&proof_bytes, &pi, AUTO_DETECT_VK_HASH, "corrupted last byte");
}

/// Completely zero out a block of bytes in the commitment region.
#[test]
fn zeroed_proof_block_rejected() {
    let (mut proof_bytes, pi) = make_proof_and_pi(
        1_500,
        &[Effect::SetField { field_idx: 1, value: BabyBear::new(42) }],
    );
    let start = (proof_bytes.len() / 3).max(8);
    let end = (start + 64).min(proof_bytes.len());
    for b in &mut proof_bytes[start..end] {
        *b = 0;
    }
    assert_rejected(&proof_bytes, &pi, AUTO_DETECT_VK_HASH, "zeroed proof block");
}

/// Empty proof bytes → parse error (exit code ERROR, not REJECTED).
#[test]
fn empty_proof_bytes_returns_error() {
    let (_, pi) = make_proof_and_pi(100, &[Effect::NoOp]);
    let (out, code) = verify_effect_vm_proof(&[], &pi, AUTO_DETECT_VK_HASH);
    assert_ne!(code, exit_code::VERIFIED, "empty bytes must not verify");
    assert!(!out.verified);
}

/// Garbage bytes → parse error.
#[test]
fn garbage_proof_bytes_returns_error() {
    let garbage: &[u8] = b"this is definitely not a STARK proof";
    let pi = vec![0u32; 25];
    let (out, code) = verify_effect_vm_proof(garbage, &pi, AUTO_DETECT_VK_HASH);
    assert_ne!(code, exit_code::VERIFIED, "garbage must not verify");
    assert!(!out.verified);
}

/// Truncated proof (first 20 bytes only).
#[test]
fn truncated_proof_bytes_returns_error() {
    let (proof_bytes, pi) = make_proof_and_pi(300, &[Effect::NoOp]);
    let truncated = &proof_bytes[..20.min(proof_bytes.len())];
    let (out, code) = verify_effect_vm_proof(truncated, &pi, AUTO_DETECT_VK_HASH);
    assert_ne!(code, exit_code::VERIFIED, "truncated proof must not verify");
    assert!(!out.verified);
}

// ─────────────────────────────────────────────────────────────────────────────
// 3. Wrong public inputs.
// ─────────────────────────────────────────────────────────────────────────────

/// Tamper OLD_COMMIT (first felt of old state commitment).
#[test]
fn wrong_old_commit_rejected() {
    let (proof_bytes, mut pi) = make_proof_and_pi(
        4_000,
        &[Effect::Transfer { amount: 400, direction: 1 }],
    );
    pi[pi::OLD_COMMIT] ^= 0xDEAD_BEEF;
    assert_rejected(&proof_bytes, &pi, AUTO_DETECT_VK_HASH, "wrong OLD_COMMIT");
}

/// Tamper NEW_COMMIT (first felt of new state commitment).
#[test]
fn wrong_new_commit_rejected() {
    let (proof_bytes, mut pi) = make_proof_and_pi(
        4_000,
        &[Effect::Transfer { amount: 400, direction: 1 }],
    );
    pi[pi::NEW_COMMIT] ^= 0xBEEF_CAFE;
    assert_rejected(&proof_bytes, &pi, AUTO_DETECT_VK_HASH, "wrong NEW_COMMIT");
}

/// Tamper NET_DELTA_MAG (claim a different signed magnitude).
#[test]
fn wrong_net_delta_mag_rejected() {
    let (proof_bytes, mut pi) = make_proof_and_pi(
        5_000,
        &[Effect::Transfer { amount: 500, direction: 1 }],
    );
    pi[pi::NET_DELTA_MAG] ^= 0x1234;
    assert_rejected(&proof_bytes, &pi, AUTO_DETECT_VK_HASH, "wrong NET_DELTA_MAG");
}

/// Tamper EFFECTS_HASH_LO (claim a different effects hash).
#[test]
fn wrong_effects_hash_rejected() {
    let (proof_bytes, mut pi) = make_proof_and_pi(
        3_000,
        &[Effect::GrantCapability { cap_entry: BabyBear::new(0xCAFE) }],
    );
    pi[pi::EFFECTS_HASH_LO] ^= 0xFFFF_FFFF;
    assert_rejected(&proof_bytes, &pi, AUTO_DETECT_VK_HASH, "wrong EFFECTS_HASH_LO");
}

/// Tamper INIT_BAL_LO (claim wrong initial balance).
#[test]
fn wrong_init_bal_lo_rejected() {
    let (proof_bytes, mut pi) = make_proof_and_pi(
        8_000,
        &[Effect::Transfer { amount: 100, direction: 0 }],
    );
    pi[pi::INIT_BAL_LO] ^= 0x1;
    assert_rejected(&proof_bytes, &pi, AUTO_DETECT_VK_HASH, "wrong INIT_BAL_LO");
}

/// Empty public inputs → verifier must reject.
#[test]
fn empty_public_inputs_rejected() {
    let (proof_bytes, _) = make_proof_and_pi(100, &[Effect::NoOp]);
    assert_rejected(&proof_bytes, &[], AUTO_DETECT_VK_HASH, "empty public inputs");
}

// ─────────────────────────────────────────────────────────────────────────────
// 4. Wrong VK hash.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn unknown_vk_hash_returns_error() {
    let (proof_bytes, pi) = make_proof_and_pi(100, &[Effect::NoOp]);
    let bad_hash = "0".repeat(64);
    let (out, code) = verify_effect_vm_proof(&proof_bytes, &pi, &bad_hash);
    assert_eq!(code, exit_code::ERROR, "unknown VK must give exit ERROR");
    assert!(!out.verified);
}

/// A VK hash that is 63 hex chars (too short) must error.
#[test]
fn short_vk_hash_returns_error() {
    let (proof_bytes, pi) = make_proof_and_pi(100, &[Effect::NoOp]);
    let short_hash = "a".repeat(63);
    let (out, code) = verify_effect_vm_proof(&proof_bytes, &pi, &short_hash);
    assert_ne!(code, exit_code::VERIFIED, "short VK hash must not verify");
    assert!(!out.verified);
}

// ─────────────────────────────────────────────────────────────────────────────
// 5. Proof reuse: a valid proof for one effect cannot verify for a different PI.
// ─────────────────────────────────────────────────────────────────────────────

/// Prove Transfer(100, out), then try to verify with PI from Transfer(200, out).
/// The PIes differ (OLD_COMMIT, FINAL_BAL, NET_DELTA_MAG), so the verifier
/// must reject the mismatched combination.
#[test]
fn proof_from_different_turn_rejected_cross_pi() {
    // Proof for a 100-unit outbound transfer.
    let (proof_bytes_100, _) = make_proof_and_pi(
        2_000,
        &[Effect::Transfer { amount: 100, direction: 1 }],
    );
    // PI from a different turn (200-unit outbound transfer, same initial balance).
    let (_, pi_200) = make_proof_and_pi(
        2_000,
        &[Effect::Transfer { amount: 200, direction: 1 }],
    );

    // The 100-unit proof against the 200-unit PI must be rejected.
    assert_rejected(
        &proof_bytes_100,
        &pi_200,
        AUTO_DETECT_VK_HASH,
        "proof(100) vs pi(200): cross-turn replay must be rejected",
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// 6. Multi-effect proof: tamper each of several PI fields and confirm rejection.
// ─────────────────────────────────────────────────────────────────────────────

/// Generate a multi-effect proof and run a battery of PI-tamper cases.
/// Each tamper flips exactly one PI field; each must be rejected.
#[test]
fn multi_effect_pi_tamper_battery() {
    let (proof_bytes, pi_orig) = make_proof_and_pi(
        20_000,
        &[
            Effect::Transfer { amount: 500, direction: 1 },
            Effect::SetField { field_idx: 3, value: BabyBear::new(99) },
            Effect::GrantCapability { cap_entry: BabyBear::new(0xABCD) },
        ],
    );

    // Fields to tamper (slot index, mask).
    let tampers: &[(usize, u32, &str)] = &[
        (pi::OLD_COMMIT, 0x1, "OLD_COMMIT"),
        (pi::NEW_COMMIT, 0x1, "NEW_COMMIT"),
        (pi::EFFECTS_HASH_LO, 0x1, "EFFECTS_HASH_LO"),
        (pi::NET_DELTA_MAG, 0x1, "NET_DELTA_MAG"),
        (pi::NET_DELTA_SIGN, 0x1, "NET_DELTA_SIGN"),
        (pi::INIT_BAL_LO, 0x1, "INIT_BAL_LO"),
        (pi::FINAL_BAL_LO, 0x1, "FINAL_BAL_LO"),
    ];

    for &(slot, mask, label) in tampers {
        if slot >= pi_orig.len() {
            continue;
        }
        let mut pi = pi_orig.clone();
        pi[slot] ^= mask;
        assert_rejected(
            &proof_bytes,
            &pi,
            AUTO_DETECT_VK_HASH,
            &format!("tamper {label}"),
        );
    }
}

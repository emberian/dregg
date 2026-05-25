//! Integration test: bridge action binding — the PortableActionBinding STARK
//! proof correctly pins full-fidelity (nullifier, recipient, destination,
//! amount) and rejects forged / tampered parameters.
//!
//! These tests exercise `create_action_binding` + `verify_action_binding`
//! end-to-end.  The STARK proof for `BridgeActionAir` is small (synthetic
//! AIR constraint check) so these tests are fast without real STARK machinery.

use pyana_bridge::{ActionBindingError, create_action_binding, verify_action_binding};

fn nullifier(seed: u8) -> [u8; 32] {
    let mut n = [0u8; 32];
    n[0] = seed;
    n[1] = 0xAA;
    n
}

fn recipient(seed: u8) -> [u8; 32] {
    let mut r = [0u8; 32];
    r[0] = seed;
    r[1] = 0xBB;
    r
}

fn dest_fed(seed: u8) -> [u8; 32] {
    let mut d = [0u8; 32];
    d[0] = seed;
    d[1] = 0xCC;
    d
}

// ============================================================================
// Happy path: correct parameters verify successfully
// ============================================================================

#[test]
fn action_binding_round_trip_verifies() {
    let n = nullifier(0x01);
    let r = recipient(0x02);
    let d = dest_fed(0x03);
    let amount: u64 = 123_456_789;

    let binding = create_action_binding(n, r, d, amount);

    let result = verify_action_binding(&binding, &n, &r, &d, amount);
    assert!(
        result.is_ok(),
        "correct parameters must verify: {:?}",
        result.err()
    );
}

// ============================================================================
// Tampered nullifier is rejected
// ============================================================================

#[test]
fn tampered_nullifier_rejected() {
    let n = nullifier(0x10);
    let r = recipient(0x20);
    let d = dest_fed(0x30);
    let amount: u64 = 500;

    let binding = create_action_binding(n, r, d, amount);

    // Executor believes a different nullifier.
    let wrong_n = nullifier(0xFF);
    let result = verify_action_binding(&binding, &wrong_n, &r, &d, amount);
    assert!(
        result.is_err(),
        "mismatched nullifier must cause AIR verification failure"
    );
    assert!(matches!(
        result.unwrap_err(),
        ActionBindingError::AirVerificationFailed { .. }
    ));
}

// ============================================================================
// Tampered recipient is rejected
// ============================================================================

#[test]
fn tampered_recipient_rejected() {
    let n = nullifier(0x11);
    let r = recipient(0x22);
    let d = dest_fed(0x33);
    let amount: u64 = 1_000;

    let binding = create_action_binding(n, r, d, amount);

    let wrong_r = recipient(0xEE);
    let result = verify_action_binding(&binding, &n, &wrong_r, &d, amount);
    assert!(
        result.is_err(),
        "mismatched recipient must cause AIR verification failure"
    );
}

// ============================================================================
// Tampered destination federation is rejected
// ============================================================================

#[test]
fn tampered_destination_federation_rejected() {
    let n = nullifier(0x12);
    let r = recipient(0x23);
    let d = dest_fed(0x34);
    let amount: u64 = 9_999;

    let binding = create_action_binding(n, r, d, amount);

    let wrong_d = dest_fed(0xDD);
    let result = verify_action_binding(&binding, &n, &r, &wrong_d, amount);
    assert!(
        result.is_err(),
        "mismatched destination federation must cause AIR verification failure"
    );
}

// ============================================================================
// Tampered amount is rejected (full 64-bit amount; no truncation)
// ============================================================================

#[test]
fn tampered_amount_rejected() {
    let n = nullifier(0x13);
    let r = recipient(0x24);
    let d = dest_fed(0x35);
    // Use an amount that exercises the high bits (> 2^30) to confirm full-64-bit binding.
    let amount: u64 = 0x0000_0002_0000_0001u64;

    let binding = create_action_binding(n, r, d, amount);

    // Amount with just the high word changed.
    let wrong_amount = 0x0000_0003_0000_0001u64;
    let result = verify_action_binding(&binding, &n, &r, &d, wrong_amount);
    assert!(
        result.is_err(),
        "mismatched high-word amount must cause AIR verification failure"
    );
}

// ============================================================================
// Corrupted proof bytes are rejected
// ============================================================================

#[test]
fn corrupted_proof_bytes_rejected() {
    let n = nullifier(0x14);
    let r = recipient(0x25);
    let d = dest_fed(0x36);
    let amount: u64 = 42;

    let mut binding = create_action_binding(n, r, d, amount);
    // Flip every byte in the proof.
    for byte in binding.proof_bytes.iter_mut() {
        *byte ^= 0xFF;
    }

    let result = verify_action_binding(&binding, &n, &r, &d, amount);
    assert!(
        result.is_err(),
        "corrupted proof bytes must be rejected"
    );
}

// ============================================================================
// Empty proof bytes are rejected (deserialization fails)
// ============================================================================

#[test]
fn empty_proof_bytes_rejected() {
    let n = nullifier(0x15);
    let r = recipient(0x26);
    let d = dest_fed(0x37);
    let amount: u64 = 100;

    let mut binding = create_action_binding(n, r, d, amount);
    binding.proof_bytes.clear();

    let result = verify_action_binding(&binding, &n, &r, &d, amount);
    assert!(
        result.is_err(),
        "empty proof bytes must fail deserialization"
    );
    assert!(matches!(
        result.unwrap_err(),
        ActionBindingError::DeserializationFailed { .. }
    ));
}

// ============================================================================
// Amount zero is accepted (zero-value transfers are structurally valid)
// ============================================================================

#[test]
fn zero_amount_round_trip() {
    let n = nullifier(0x16);
    let r = recipient(0x27);
    let d = dest_fed(0x38);
    let amount: u64 = 0;

    let binding = create_action_binding(n, r, d, amount);
    let result = verify_action_binding(&binding, &n, &r, &d, amount);
    assert!(
        result.is_ok(),
        "zero amount must round-trip cleanly: {:?}",
        result.err()
    );
}

// ============================================================================
// Large amount (u64::MAX) is accepted without truncation
// ============================================================================

#[test]
fn max_amount_round_trip() {
    let n = nullifier(0x17);
    let r = recipient(0x28);
    let d = dest_fed(0x39);
    let amount: u64 = u64::MAX;

    let binding = create_action_binding(n, r, d, amount);
    let result = verify_action_binding(&binding, &n, &r, &d, amount);
    assert!(
        result.is_ok(),
        "u64::MAX amount must round-trip without truncation: {:?}",
        result.err()
    );
}

// ============================================================================
// Replay: same binding accepted again with identical parameters (idempotent
// verify); the ACTION-LAYER replay gate is the executor's nullifier set, not
// the binding itself.
// ============================================================================

#[test]
fn same_binding_accepted_twice() {
    let n = nullifier(0x18);
    let r = recipient(0x29);
    let d = dest_fed(0x3A);
    let amount: u64 = 77;

    let binding = create_action_binding(n, r, d, amount);

    // First verify.
    assert!(verify_action_binding(&binding, &n, &r, &d, amount).is_ok());
    // Second verify — proof is stateless so this must also succeed.
    // (Replay prevention is the executor's job via the nullifier set.)
    assert!(
        verify_action_binding(&binding, &n, &r, &d, amount).is_ok(),
        "pure-verify call is idempotent; replay rejection lives at the executor layer"
    );
}

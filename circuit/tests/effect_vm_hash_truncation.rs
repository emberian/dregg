//! Adversarial regression tests for the EffectVM 32-byte hash-truncation fix
//! (effect-vm-hash-truncation lane, 2026-05-28).
//!
//! Before the fix, the executor + SDK projectors folded only the FIRST 4 BYTES
//! of each 32-byte hash/field element into a BabyBear (`hash_to_bb` /
//! `field_element_to_bb`). Two effects differing ONLY in bytes [4..32]
//! collapsed to the IDENTICAL circuit-side identifier — identical effect
//! params, identical `compute_effects_hash`, identical `PI[EFFECTS_HASH]` —
//! and produced interchangeable proofs.
//!
//! These tests pin the new behaviour: the shared canonical fold
//! `dregg_circuit::effect_vm::fold_bytes32_to_bb` folds ALL 32 bytes, so two
//! values differing above byte 4 yield distinct felts, distinct effects
//! hashes, and distinct EffectVM public inputs.
//!
//! Each `*_would_have_passed_before` assertion documents the OLD truncating
//! behaviour and shows it would have FAILED to distinguish (i.e. the test
//! fails before the fix, passes after).

use dregg_circuit::effect_vm::{
    CellState, Effect as VmEffect, compute_effects_hash, compute_effects_hash_4,
    fold_bytes32_to_bb, generate_effect_vm_trace, pi,
};
use dregg_circuit::field::BabyBear;

/// The OLD truncating projection — take only the first 4 bytes. Kept here so
/// the test can demonstrate the collision the fix removes.
fn old_truncating_hash_to_bb(h: &[u8; 32]) -> BabyBear {
    let v = u32::from_le_bytes([h[0], h[1], h[2], h[3]]) % dregg_circuit::field::BABYBEAR_P;
    BabyBear::new(v)
}

/// Two 32-byte values that agree on bytes [0..4] but differ above byte 4.
fn high_byte_pair() -> ([u8; 32], [u8; 32]) {
    let mut a = [0u8; 32];
    let mut b = [0u8; 32];
    // Identical low 4 bytes (the only bytes the OLD code looked at).
    for (i, v) in [0x11u8, 0x22, 0x33, 0x44].into_iter().enumerate() {
        a[i] = v;
        b[i] = v;
    }
    // Differ in the HIGH bytes only.
    a[5] = 0xAA;
    a[17] = 0xBB;
    a[31] = 0xCC;
    b[5] = 0x55;
    b[17] = 0x66;
    b[31] = 0x77;
    (a, b)
}

#[test]
fn fold_distinguishes_values_differing_above_byte_4() {
    let (a, b) = high_byte_pair();

    // OLD behaviour: collision (this is the bug). Demonstrate it so the test's
    // meaning is unambiguous.
    assert_eq!(
        old_truncating_hash_to_bb(&a),
        old_truncating_hash_to_bb(&b),
        "sanity: the OLD 4-byte truncation collides on this pair (that was the bug)",
    );

    // NEW behaviour: the canonical fold binds all 32 bytes, so it MUST differ.
    assert_ne!(
        fold_bytes32_to_bb(&a),
        fold_bytes32_to_bb(&b),
        "fold_bytes32_to_bb must distinguish values differing above byte 4",
    );

    // Equal inputs still fold equally (determinism).
    assert_eq!(fold_bytes32_to_bb(&a), fold_bytes32_to_bb(&a));

    // Values that differ ONLY in bytes [0..4] are also distinguished (the fold
    // is a function of the whole value, not just the high bytes).
    let mut c = a;
    c[0] ^= 0x01;
    assert_ne!(fold_bytes32_to_bb(&a), fold_bytes32_to_bb(&c));
}

#[test]
fn fold_is_backward_compatible_for_low_4_byte_only_values() {
    // When bytes [4..32] are all zero, the fold collapses to the low-4-byte
    // value (Horner with all-zero high limbs). This keeps every pre-existing
    // test/effect that used short hashes byte-for-byte identical.
    let mut only_low = [0u8; 32];
    only_low[..4].copy_from_slice(&0xDEAD_BEEFu32.to_le_bytes());
    assert_eq!(
        fold_bytes32_to_bb(&only_low),
        old_truncating_hash_to_bb(&only_low),
        "low-4-byte-only values must fold to the same felt the old code produced",
    );
}

#[test]
fn grant_capability_effects_hash_binds_full_32_bytes() {
    // GrantCapability carries `cap_entry: BabyBear`, populated via the
    // projector's `hash_to_bb`. With the fix, two cap hashes differing only
    // above byte 4 produce DIFFERENT cap_entry felts and therefore DIFFERENT
    // effects hashes — non-interchangeable proofs.
    let (a, b) = high_byte_pair();

    let eff_a = vec![VmEffect::GrantCapability {
        cap_entry: fold_bytes32_to_bb(&a),
    }];
    let eff_b = vec![VmEffect::GrantCapability {
        cap_entry: fold_bytes32_to_bb(&b),
    }];

    let (lo_a, _) = compute_effects_hash(&eff_a);
    let (lo_b, _) = compute_effects_hash(&eff_b);
    assert_ne!(
        lo_a, lo_b,
        "GrantCapability effects_hash must differ when cap hashes differ above byte 4",
    );

    // And the OLD truncation would have produced identical cap_entry felts:
    let old_a = old_truncating_hash_to_bb(&a);
    let old_b = old_truncating_hash_to_bb(&b);
    let (old_lo_a, _) = compute_effects_hash(&[VmEffect::GrantCapability { cap_entry: old_a }]);
    let (old_lo_b, _) = compute_effects_hash(&[VmEffect::GrantCapability { cap_entry: old_b }]);
    assert_eq!(
        old_lo_a, old_lo_b,
        "sanity: OLD truncation collapsed both to the same effects_hash (the bug)",
    );
}

#[test]
fn notespend_effect_vm_public_inputs_differ_for_high_byte_nullifiers() {
    // End-to-end through the trace generator + PI extraction: two NoteSpend
    // effects whose nullifiers differ only above byte 4 must yield different
    // EffectVM `PI[EFFECTS_HASH]` (the proof's binding to the spent note).
    let (a, b) = high_byte_pair();

    let mut initial = CellState::new(1_000_000, 0);
    initial.refresh_commitment();

    let eff_a = vec![VmEffect::NoteSpend {
        nullifier: fold_bytes32_to_bb(&a),
        value: 500,
    }];
    let eff_b = vec![VmEffect::NoteSpend {
        nullifier: fold_bytes32_to_bb(&b),
        value: 500,
    }];

    let (_trace_a, pi_a) = generate_effect_vm_trace(&initial, &eff_a);
    let (_trace_b, pi_b) = generate_effect_vm_trace(&initial, &eff_b);

    // The EFFECTS_HASH slot (4 felts) MUST differ.
    let eh_a = &pi_a[pi::EFFECTS_HASH_BASE..pi::EFFECTS_HASH_BASE + pi::EFFECTS_HASH_LEN];
    let eh_b = &pi_b[pi::EFFECTS_HASH_BASE..pi::EFFECTS_HASH_BASE + pi::EFFECTS_HASH_LEN];
    assert_ne!(
        eh_a, eh_b,
        "EffectVM PI[EFFECTS_HASH] must differ for nullifiers differing above byte 4 \
         (non-interchangeable proofs)",
    );

    // Belt-and-suspenders: the 4-felt effects hash helper agrees with the PI.
    let h4_a = compute_effects_hash_4(&eff_a);
    let h4_b = compute_effects_hash_4(&eff_b);
    assert_ne!(h4_a, h4_b);
    assert_eq!(&h4_a[..], eh_a);
    assert_eq!(&h4_b[..], eh_b);
}

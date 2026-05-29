//! Adversarial tests for FULL-WIDTH (256-bit-per-field) note-commitment binding
//! in the note-spending STARK AIR.
//!
//! # The defect these tests pin
//!
//! The legacy note-spending AIR recomputed the in-circuit commitment as
//! `hash_many([owner, value, asset_type, creation_nonce, randomness])` over FIVE
//! single BabyBear felts. The SDK/witness builder collapsed each 32-byte field
//! (owner / creation_nonce / randomness) into one felt via either its first
//! 4 bytes or a fixed compression, and each u64 (value / asset_type) into its
//! low 32 bits. As a result, two notes that differed ONLY in bytes ABOVE the
//! first chunk of owner / creation_nonce / randomness — or above bit 32 of
//! asset_type — hashed to the SAME in-circuit commitment. An attacker could
//! therefore spend one note's value against a DIFFERENT note's identity in the
//! circuit.
//!
//! # The fix
//!
//! `NoteSpendingWitness` now carries the FULL 28-limb Poseidon2 preimage
//! (`owner[8] ‖ value[lo,hi] ‖ asset_type[lo,hi] ‖ creation_nonce[8] ‖
//! randomness[8]`) — the same limb layout as
//! `dregg_cell::Note::poseidon2_commitment`. The DSL AIR binds `col::COMMITMENT`
//! to a chained Poseidon2 `hash_fact` sponge over all 28 limbs (constraints
//! C2a..C2g + the `col::COMMITMENT == COMMITMENT_FULL` equality), and the
//! nullifier + Merkle membership chain off that full-width commitment. Two notes
//! differing in ANY byte of ANY field now produce a distinct in-circuit
//! commitment.
//!
//! These tests construct witnesses from RAW note bytes via `from_note_limbs` and
//! assert: (a) flipping a HIGH byte of owner / creation_nonce / randomness
//! changes the in-circuit commitment AND the resulting proof does not verify
//! against the other note's nullifier/root; (b) value/asset_type high-32-bit
//! differences likewise bind.
//!
//! FAIL-before / PASS-after: against the legacy 5-felt AIR (single-felt owner/
//! nonce/randomness via first-4-bytes, u64 low-32 value/asset), the high-byte
//! variants would collapse to the SAME commitment, so the "distinct commitment"
//! and "cross-note proof rejected" assertions FAIL. With the 28-limb binding
//! they PASS.

use dregg_circuit::dsl::note_spending::{
    dsl_commitment, dsl_merkle_root, dsl_nullifier, prove_note_spend_dsl, verify_note_spend_dsl,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::note_spending_air::{NoteSpendingWitness, test_spending_key};

/// Build a depth-`depth` witness from raw note fields with deterministic
/// siblings (mirrors `create_test_witness`'s Merkle-path shape but lets us
/// control every byte of owner / creation_nonce / randomness and the full u64
/// value / asset_type).
fn witness_from_bytes(
    owner: [u8; 32],
    value: u64,
    asset_type: u64,
    creation_nonce: [u8; 32],
    randomness: [u8; 32],
    depth: usize,
) -> NoteSpendingWitness {
    use dregg_circuit::poseidon2::hash_many;
    let seed = BabyBear::new(owner[0] as u32 + 1);
    let mut merkle_siblings = Vec::with_capacity(depth);
    let mut merkle_positions = Vec::with_capacity(depth);
    for i in 0..depth {
        let pos = (i % 4) as u8;
        let siblings = [
            hash_many(&[BabyBear::new((i * 3 + 1) as u32), seed]),
            hash_many(&[BabyBear::new((i * 3 + 2) as u32), seed]),
            hash_many(&[BabyBear::new((i * 3 + 3) as u32), seed]),
        ];
        merkle_siblings.push(siblings);
        merkle_positions.push(pos);
    }
    NoteSpendingWitness::from_note_limbs(
        &owner,
        value,
        asset_type,
        &creation_nonce,
        &randomness,
        test_spending_key(0xA5A5),
        merkle_siblings,
        merkle_positions,
    )
}

/// Generate a proof for `w` and verify it against the (nullifier, root, value,
/// asset_type) of `target`. Returns whether verification succeeds.
fn proof_of_verifies_against(
    prover_w: &NoteSpendingWitness,
    target_w: &NoteSpendingWitness,
) -> bool {
    let proof = prove_note_spend_dsl(prover_w);
    verify_note_spend_dsl(
        dsl_nullifier(target_w),
        dsl_merkle_root(target_w),
        target_w.value,
        target_w.asset_type,
        &proof,
    )
    .is_ok()
}

/// Two notes identical except a single byte of `owner` at the given (high) index
/// must produce DISTINCT in-circuit commitments, and a spend proof for one must
/// NOT verify against the other's nullifier/root.
fn assert_owner_byte_binds(byte_index: usize) {
    let base_owner = [7u8; 32];
    let mut alt_owner = base_owner;
    alt_owner[byte_index] ^= 0xFF; // flip a HIGH byte (index >= 4)

    let nonce = [3u8; 32];
    let rand = [9u8; 32];
    let w1 = witness_from_bytes(base_owner, 500, 1, nonce, rand, 2);
    let w2 = witness_from_bytes(alt_owner, 500, 1, nonce, rand, 2);

    assert_ne!(
        dsl_commitment(&w1),
        dsl_commitment(&w2),
        "owner byte[{byte_index}] must change the in-circuit commitment (legacy 5-felt AIR collided here)"
    );

    // Honest proof verifies against its own identity.
    assert!(
        proof_of_verifies_against(&w1, &w1),
        "honest proof must verify against its own note"
    );
    // Cross-note: proof for w1 must NOT verify against w2's identity.
    assert!(
        !proof_of_verifies_against(&w1, &w2),
        "owner byte[{byte_index}] differing: w1's proof must NOT verify against w2"
    );
}

#[test]
fn owner_high_byte_8_binds() {
    assert_owner_byte_binds(8);
}

#[test]
fn owner_high_byte_16_binds() {
    assert_owner_byte_binds(16);
}

#[test]
fn owner_high_byte_31_binds() {
    assert_owner_byte_binds(31);
}

fn assert_nonce_byte_binds(byte_index: usize) {
    let owner = [7u8; 32];
    let base_nonce = [3u8; 32];
    let mut alt_nonce = base_nonce;
    alt_nonce[byte_index] ^= 0xFF;
    let rand = [9u8; 32];

    let w1 = witness_from_bytes(owner, 500, 1, base_nonce, rand, 2);
    let w2 = witness_from_bytes(owner, 500, 1, alt_nonce, rand, 2);

    assert_ne!(
        dsl_commitment(&w1),
        dsl_commitment(&w2),
        "creation_nonce byte[{byte_index}] must change the in-circuit commitment"
    );
    assert!(
        !proof_of_verifies_against(&w1, &w2),
        "creation_nonce byte[{byte_index}] differing: cross-note proof must be rejected"
    );
}

#[test]
fn creation_nonce_high_byte_8_binds() {
    assert_nonce_byte_binds(8);
}

#[test]
fn creation_nonce_high_byte_16_binds() {
    assert_nonce_byte_binds(16);
}

#[test]
fn creation_nonce_high_byte_31_binds() {
    assert_nonce_byte_binds(31);
}

fn assert_randomness_byte_binds(byte_index: usize) {
    let owner = [7u8; 32];
    let nonce = [3u8; 32];
    let base_rand = [9u8; 32];
    let mut alt_rand = base_rand;
    alt_rand[byte_index] ^= 0xFF;

    let w1 = witness_from_bytes(owner, 500, 1, nonce, base_rand, 2);
    let w2 = witness_from_bytes(owner, 500, 1, nonce, alt_rand, 2);

    assert_ne!(
        dsl_commitment(&w1),
        dsl_commitment(&w2),
        "randomness byte[{byte_index}] must change the in-circuit commitment"
    );
    assert!(
        !proof_of_verifies_against(&w1, &w2),
        "randomness byte[{byte_index}] differing: cross-note proof must be rejected"
    );
}

#[test]
fn randomness_high_byte_8_binds() {
    assert_randomness_byte_binds(8);
}

#[test]
fn randomness_high_byte_16_binds() {
    assert_randomness_byte_binds(16);
}

#[test]
fn randomness_high_byte_31_binds() {
    assert_randomness_byte_binds(31);
}

/// asset_type values differing ONLY above bit 32 must produce distinct in-circuit
/// commitments (the legacy AIR bound only the low 32 bits of asset_type, so two
/// asset_types sharing the low 32 bits collided).
#[test]
fn asset_type_high_32_bits_bind() {
    let owner = [7u8; 32];
    let nonce = [3u8; 32];
    let rand = [9u8; 32];
    let low: u64 = 0x1234_5678;
    let asset_a = low | (1u64 << 40);
    let asset_b = low | (1u64 << 50);
    assert_eq!(asset_a as u32, asset_b as u32, "low 32 bits must collide");

    let w1 = witness_from_bytes(owner, 500, asset_a, nonce, rand, 2);
    let w2 = witness_from_bytes(owner, 500, asset_b, nonce, rand, 2);

    assert_ne!(
        dsl_commitment(&w1),
        dsl_commitment(&w2),
        "asset_type high-32-bit difference must change the in-circuit commitment"
    );
    assert!(
        !proof_of_verifies_against(&w1, &w2),
        "asset_type high bits differing: cross-note proof must be rejected"
    );
}

/// value amounts differing above bit 30 (same low-30 limb) must produce distinct
/// in-circuit commitments now that the value-hi limb is folded into the
/// commitment preimage.
#[test]
fn value_high_bits_bind_in_commitment() {
    let owner = [7u8; 32];
    let nonce = [3u8; 32];
    let rand = [9u8; 32];
    let low: u64 = 0x2BCDE;
    let value_a = low | (1u64 << 35);
    let value_b = low | (1u64 << 45);
    assert_eq!(
        (value_a & ((1u64 << 30) - 1)),
        (value_b & ((1u64 << 30) - 1)),
        "low-30 limbs must collide"
    );

    let w1 = witness_from_bytes(owner, value_a, 1, nonce, rand, 2);
    let w2 = witness_from_bytes(owner, value_b, 1, nonce, rand, 2);

    assert_ne!(
        dsl_commitment(&w1),
        dsl_commitment(&w2),
        "value high bits (above bit 30) must change the in-circuit commitment"
    );
    assert!(
        !proof_of_verifies_against(&w1, &w2),
        "value high bits differing: cross-note proof must be rejected"
    );
}

/// Sanity: two notes with IDENTICAL fields produce the SAME commitment,
/// nullifier and root (the binding is a function, not noise).
#[test]
fn identical_notes_same_commitment() {
    let owner = [7u8; 32];
    let nonce = [3u8; 32];
    let rand = [9u8; 32];
    let w1 = witness_from_bytes(owner, 500, 1, nonce, rand, 2);
    let w2 = witness_from_bytes(owner, 500, 1, nonce, rand, 2);
    assert_eq!(dsl_commitment(&w1), dsl_commitment(&w2));
    assert_eq!(dsl_nullifier(&w1), dsl_nullifier(&w2));
    assert_eq!(dsl_merkle_root(&w1), dsl_merkle_root(&w2));
    assert!(proof_of_verifies_against(&w1, &w2));
}

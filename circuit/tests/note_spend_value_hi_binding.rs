//! Adversarial tests for the note-spending full-u64 value binding
//! (30-bit-trunc fix, CAVEAT-LAYER-COVERAGE.md §6.5).
//!
//! Pre-fix, the bridge-mint executor path verified the note-spending STARK
//! proof against `value & ((1<<30)-1)` only — the upper 34 bits of the u64
//! amount were discarded. Two amounts that share the low 30 bits but differ
//! above bit 30 produced identical public inputs, so a single proof bound a
//! coarse equivalence class of amounts.
//!
//! The fix adds a `VALUE_HI` trace column + PI slot (`pi::VALUE_HI`) bound by
//! a row-0 boundary constraint. The bridge path now splits the u64 into
//! (low 30, upper 34) and binds BOTH limbs. These tests prove a proof minted
//! for a high-bit amount is REJECTED when verified against the low-30-bit
//! truncation, and vice versa.

use dregg_circuit::dsl::note_spending::{
    dsl_merkle_root, dsl_nullifier, prove_note_spend_dsl, prove_note_spend_dsl_full,
    verify_note_spend_dsl_full, witness_with_value_hi,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::note_spending_air::{create_test_witness, test_spending_key};

/// Split a u64 amount into the (low-30, upper-34) BabyBear limb pair the
/// bridge executor path uses.
fn u64_limbs(v: u64) -> (BabyBear, BabyBear) {
    (
        BabyBear::new((v & ((1u64 << 30) - 1)) as u32),
        BabyBear::new((v >> 30) as u32),
    )
}

/// Build a witness whose committed `value` felt equals the low-30 limb of the
/// given u64 amount (the bridge path commits the low limb into the note).
fn witness_for_amount(amount: u64) -> dregg_circuit::note_spending_air::NoteSpendingWitness {
    let (lo, _hi) = u64_limbs(amount);
    create_test_witness(
        BabyBear::new(7),
        lo,
        BabyBear::new(1), // asset_type
        test_spending_key(42),
        2,
    )
}

/// Honest round-trip: a high-bit amount verifies against its own full limbs.
#[test]
fn full_value_honest_roundtrip() {
    let amount: u64 = (1u64 << 50) | 0xABCD;
    let (lo, hi) = u64_limbs(amount);
    let w = witness_for_amount(amount);
    let proof = prove_note_spend_dsl_full(&w, hi);
    // value_hi is now folded into the FULL-WIDTH commitment, so the nullifier
    // and Merkle root must be computed from the value_hi-bearing witness.
    let wf = witness_with_value_hi(&w, hi);
    let root = dsl_merkle_root(&wf);
    let res = verify_note_spend_dsl_full(
        dsl_nullifier(&wf),
        root,
        lo,
        hi,
        w.asset_type,
        BabyBear::ZERO,
        &proof,
    );
    assert!(res.is_ok(), "honest full-u64 proof must verify: {res:?}");
}

/// CRITICAL: a proof minted for an amount above 2^30 must be REJECTED when the
/// verifier passes the low-30-bit truncation (high limb zero). This is exactly
/// the attack the pre-fix path silently accepted.
#[test]
fn high_bit_amount_rejected_against_truncation() {
    let amount: u64 = (1u64 << 40) | 0x1234;
    let (lo, hi) = u64_limbs(amount);
    assert_ne!(hi, BabyBear::ZERO, "test amount must exceed 2^30");

    let w = witness_for_amount(amount);
    let proof = prove_note_spend_dsl_full(&w, hi);
    let wf = witness_with_value_hi(&w, hi);
    let root = dsl_merkle_root(&wf);

    // Verifier truncates to low 30 bits (high limb = 0) — pre-fix behaviour.
    let res = verify_note_spend_dsl_full(
        dsl_nullifier(&wf),
        root,
        lo,
        BabyBear::ZERO, // truncated high limb
        w.asset_type,
        BabyBear::ZERO,
        &proof,
    );
    assert!(
        res.is_err(),
        "amount above 2^30 must NOT verify against its low-30-bit truncation"
    );
}

/// CRITICAL: two amounts sharing the low 30 bits but differing in the high
/// bits produce non-interchangeable proofs.
#[test]
fn two_amounts_same_low_distinct_high_not_interchangeable() {
    let low_shared: u64 = 0x2BCDE;
    let amount_a = low_shared | (1u64 << 35);
    let amount_b = low_shared | (1u64 << 45);
    let (lo_a, hi_a) = u64_limbs(amount_a);
    let (lo_b, hi_b) = u64_limbs(amount_b);
    assert_eq!(lo_a, lo_b, "low limbs must collide for this test");
    assert_ne!(hi_a, hi_b, "high limbs must differ for this test");

    let w = witness_for_amount(amount_a);
    let proof_a = prove_note_spend_dsl_full(&w, hi_a);
    let wf = witness_with_value_hi(&w, hi_a);
    let root = dsl_merkle_root(&wf);

    // proof_a verifies against amount_a's limbs.
    assert!(
        verify_note_spend_dsl_full(
            dsl_nullifier(&wf),
            root,
            lo_a,
            hi_a,
            w.asset_type,
            BabyBear::ZERO,
            &proof_a
        )
        .is_ok()
    );
    // But NOT against amount_b's high limb.
    assert!(
        verify_note_spend_dsl_full(
            dsl_nullifier(&wf),
            root,
            lo_b,
            hi_b,
            w.asset_type,
            BabyBear::ZERO,
            &proof_a
        )
        .is_err(),
        "proof for amount_a must not verify as amount_b (distinct high bits)"
    );
}

/// Backward-compat: the felt-sized (BabyBear-typed) prover emits value_hi == 0,
/// and verifies with a zero high limb.
#[test]
fn felt_sized_value_binds_zero_high_limb() {
    let w = create_test_witness(
        BabyBear::new(3),
        BabyBear::new(500),
        BabyBear::new(1),
        test_spending_key(9),
        2,
    );
    let proof = prove_note_spend_dsl(&w);
    let root = dsl_merkle_root(&w);
    assert!(
        verify_note_spend_dsl_full(
            dsl_nullifier(&w),
            root,
            w.value,
            BabyBear::ZERO,
            w.asset_type,
            BabyBear::ZERO,
            &proof
        )
        .is_ok()
    );
    // A non-zero high limb must be rejected (the proof committed zero).
    assert!(
        verify_note_spend_dsl_full(
            dsl_nullifier(&w),
            root,
            w.value,
            BabyBear::new(1),
            w.asset_type,
            BabyBear::ZERO,
            &proof
        )
        .is_err(),
        "felt-sized proof must reject a spurious non-zero high limb"
    );
}

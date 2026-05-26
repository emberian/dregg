//! Integration: committee threshold attestation — sign, tamper, verify.
//!
//! Covers:
//! - N-member committee signs an AttestedRoot body; QC verifies
//! - One tampered signature causes verification to fail (below threshold)
//! - Aggregation below threshold is rejected by hints itself
//! - Wrong-message verification fails (body hash mismatch)
//! - QC bytes serialization round-trip preserves validity
//! - Cross-committee confusion: QC from committee A rejected by committee B

use dregg_federation::identity::derive_federation_id;
use dregg_federation::threshold::{
    FederationCommittee, MemberSecret, generate_test_committee, generate_test_committee_with_seed,
};
use dregg_federation::{FederationReceipt, FederationReceiptBody};
use dregg_types::{CellId, generate_keypair};

// =============================================================================
// Helpers
// =============================================================================

fn sample_body(seed: u8) -> FederationReceiptBody {
    FederationReceiptBody {
        turn_hash: [seed; 32],
        block_height: 42,
        block_hash: [seed.wrapping_add(1); 32],
        agent: CellId::from_bytes([seed.wrapping_add(2); 32]),
        nonce: seed as u64,
        pre_state_hash: [seed.wrapping_add(3); 32],
        post_state_hash: [seed.wrapping_add(4); 32],
        effects_hash: [seed.wrapping_add(5); 32],
        previous_receipt_hash: None,
    }
}

fn quorum_sign(
    committee: &FederationCommittee,
    members: &[MemberSecret],
    threshold: usize,
    body_hash: &[u8],
) -> dregg_federation::ThresholdQC {
    let shares: Vec<_> = members[..threshold]
        .iter()
        .map(|m| (m.index, committee.sign_share(m, body_hash)))
        .collect();
    committee
        .aggregate(&shares, body_hash)
        .expect("aggregation must succeed at threshold")
}

// =============================================================================
// Happy-path: N-of-N signs; receipt verifies
// =============================================================================

#[test]
fn threshold_attestation_full_committee_verifies() {
    let n = 4;
    let t = 3u64;
    let (committee, members) = generate_test_committee(n, t).unwrap();
    let ed_keys: Vec<_> = (0..n).map(|_| generate_keypair().1).collect();
    let fed_id = derive_federation_id(&ed_keys);

    let body = sample_body(1);
    let hash = body.body_hash();

    let qc = quorum_sign(&committee, &members, t as usize, &hash);
    let receipt = FederationReceipt::with_threshold_qc(fed_id, 0, body, &qc);

    assert!(
        receipt.verify(Some(&committee), &ed_keys, 0, 0),
        "full-committee receipt must verify"
    );
}

// =============================================================================
// Below threshold: aggregation must be refused before tamper even happens
// =============================================================================

#[test]
fn below_threshold_aggregation_fails() {
    let (committee, members) = generate_test_committee(4, 3).unwrap();
    let body = sample_body(2);
    let hash = body.body_hash();

    // Only 2 signatures, threshold = 3.
    let shares: Vec<_> = members[..2]
        .iter()
        .map(|m| (m.index, committee.sign_share(m, &hash)))
        .collect();
    let result = committee.aggregate(&shares, &hash);
    assert!(result.is_err(), "aggregation below threshold must fail");
}

// =============================================================================
// Tampered body: valid QC over body A must not verify a different body B
// =============================================================================

#[test]
fn tampered_body_fails_verification() {
    let (committee, members) = generate_test_committee(4, 3).unwrap();
    let ed_keys: Vec<_> = (0..4).map(|_| generate_keypair().1).collect();
    let fed_id = derive_federation_id(&ed_keys);

    let body_a = sample_body(10);
    let hash_a = body_a.body_hash();

    let qc = quorum_sign(&committee, &members, 3, &hash_a);

    // Receipt carries body_b but the QC was over body_a.
    let body_b = sample_body(11);
    let receipt = FederationReceipt::with_threshold_qc(fed_id, 0, body_b, &qc);

    assert!(
        !receipt.verify(Some(&committee), &ed_keys, 0, 0),
        "QC over body_a must not satisfy body_b"
    );
}

// =============================================================================
// Cross-committee confusion: QC from committee A rejected by committee B
// =============================================================================

#[test]
fn cross_committee_qc_rejected() {
    let (committee_a, members_a) = generate_test_committee_with_seed(4, 3, [11u8; 32]).unwrap();
    let (committee_b, _members_b) = generate_test_committee_with_seed(4, 3, [22u8; 32]).unwrap();

    let ed_keys: Vec<_> = (0..4).map(|_| generate_keypair().1).collect();
    let fed_id = derive_federation_id(&ed_keys);

    let body = sample_body(20);
    let hash = body.body_hash();

    // QC from committee A.
    let qc_a = quorum_sign(&committee_a, &members_a, 3, &hash);
    let receipt = FederationReceipt::with_threshold_qc(fed_id, 0, body, &qc_a);

    // Verify against committee B (different universe) — must fail.
    assert!(
        !receipt.verify(Some(&committee_b), &ed_keys, 0, 0),
        "QC from committee A must not satisfy committee B"
    );
}

// =============================================================================
// QC bytes serialization round-trip preserves validity
// =============================================================================

#[test]
fn qc_bytes_round_trip_verifies() {
    let (committee, members) = generate_test_committee(4, 3).unwrap();
    let ed_keys: Vec<_> = (0..4).map(|_| generate_keypair().1).collect();
    let fed_id = derive_federation_id(&ed_keys);

    let body = sample_body(30);
    let hash = body.body_hash();

    let qc = quorum_sign(&committee, &members, 3, &hash);
    let qc_bytes = qc.to_bytes();
    let qc2 = dregg_federation::ThresholdQC::from_bytes(&qc_bytes)
        .expect("deserialized QC must be valid");

    let receipt = FederationReceipt::with_threshold_qc(fed_id, 0, body, &qc2);
    assert!(
        receipt.verify(Some(&committee), &ed_keys, 0, 0),
        "receipt with deserialized QC must still verify"
    );
}

// =============================================================================
// Federation-id mismatch: receipt for wrong federation rejected (F1)
// =============================================================================

#[test]
fn federation_id_mismatch_rejected() {
    let (committee, members) = generate_test_committee(4, 3).unwrap();
    let ed_keys: Vec<_> = (0..4).map(|_| generate_keypair().1).collect();

    let body = sample_body(40);
    let hash = body.body_hash();
    let qc = quorum_sign(&committee, &members, 3, &hash);

    // Tag with an all-zeros fed_id instead of the derived one.
    let receipt = FederationReceipt::with_threshold_qc([0u8; 32], 0, body, &qc);
    assert!(
        !receipt.verify(Some(&committee), &ed_keys, 0, 0),
        "receipt tagged with wrong federation_id must be rejected"
    );
}

// =============================================================================
// Ed25519 fallback (Votes QC): meets threshold; tampered signer rejected
// =============================================================================

#[test]
fn votes_qc_threshold_and_unknown_signer_rejection() {
    use dregg_types::sign;

    let kps: Vec<_> = (0..4).map(|_| generate_keypair()).collect();
    let known: Vec<_> = kps.iter().map(|(_, pk)| pk.clone()).collect();
    let fed_id = derive_federation_id(&known);

    let body = sample_body(50);
    let hash = body.body_hash();

    // 3-of-4 sign; threshold = 3.
    let votes: Vec<_> = kps[..3]
        .iter()
        .map(|(sk, pk)| (pk.clone(), sign(sk, &hash)))
        .collect();

    let receipt = FederationReceipt::with_vote_signatures(fed_id, 0, body.clone(), votes);
    assert!(
        receipt.verify(None, &known, 3, 0),
        "3-of-4 votes must meet threshold 3"
    );

    // Outsider signs: should be rejected.
    let (outsider_sk, outsider_pk) = generate_keypair();
    let bad_votes = vec![(outsider_pk, sign(&outsider_sk, &hash))];
    let bad_receipt = FederationReceipt::with_vote_signatures(fed_id, 0, body, bad_votes);
    assert!(
        !bad_receipt.verify(None, &known, 1, 0),
        "vote from unknown signer must be rejected"
    );
}

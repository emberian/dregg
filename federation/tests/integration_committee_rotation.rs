//! Integration: committee rotation — federation_id is keyed to committee; old
//! AttestedRoots still verify under the old committee VK after rotation.
//!
//! Covers:
//! - `Federation::id()` is derived as H(sorted_members || epoch)
//! - `apply_epoch_transition` recomputes the id; new id != old id
//! - Old FederationReceipt produced under epoch 0 committee verifies at epoch 0
//! - After rotation, the old receipt does NOT verify under the new committee
//!   (epoch binding check fires)
//! - Member addition changes the id; member removal also changes the id
//! - Order-independence: same members in different order produce the same id

use dregg_federation::{
    Federation, FederationReceipt, FederationReceiptBody,
    identity::derive_federation_id_with_epoch,
    threshold::{generate_test_committee, generate_test_committee_with_seed},
    types::{PublicKey, SigningKey, generate_keypair, sign},
};
use dregg_types::CellId;

// =============================================================================
// Helpers
// =============================================================================

fn sample_body(seed: u8) -> FederationReceiptBody {
    FederationReceiptBody {
        turn_hash: [seed; 32],
        block_height: 1,
        block_hash: [seed.wrapping_add(1); 32],
        agent: CellId::from_bytes([seed.wrapping_add(2); 32]),
        nonce: seed as u64,
        pre_state_hash: [seed.wrapping_add(3); 32],
        post_state_hash: [seed.wrapping_add(4); 32],
        effects_hash: [seed.wrapping_add(5); 32],
        previous_receipt_hash: None,
    }
}

fn pk_vec(n: usize) -> Vec<(SigningKey, PublicKey)> {
    (0..n).map(|_| generate_keypair()).collect()
}

// =============================================================================
// federation_id is H(sorted(members) || epoch)
// =============================================================================

#[test]
fn federation_id_is_keyed_hash_of_committee_and_epoch() {
    let kps = pk_vec(3);
    let pks: Vec<PublicKey> = kps.iter().map(|(_, pk)| pk.clone()).collect();

    let fed = Federation::verifier_only(pks.clone(), 0, 2);
    let expected = derive_federation_id_with_epoch(&fed.members().to_vec(), 0);
    assert_eq!(fed.id().0, expected, "id must be BLAKE3(members || epoch)");
}

// =============================================================================
// apply_epoch_transition recomputes id; new id differs from old id
// =============================================================================

#[test]
fn epoch_rotation_produces_new_federation_id() {
    let kps0 = pk_vec(3);
    let pks0: Vec<PublicKey> = kps0.iter().map(|(_, pk)| pk.clone()).collect();

    let mut fed = Federation::verifier_only(pks0.clone(), 0, 2);
    let id_before = fed.id();

    // Add one more member and bump epoch.
    let (_, new_pk) = generate_keypair();
    let mut new_members = pks0.clone();
    new_members.push(new_pk);
    fed.apply_epoch_transition(new_members, 1, 3);

    let id_after = fed.id();
    assert_ne!(
        id_before, id_after,
        "rotation must produce a new federation_id"
    );
    assert_eq!(fed.epoch(), 1);
    assert_eq!(fed.num_members(), 4);
}

// =============================================================================
// Old receipt verifies under epoch 0; NOT under epoch 1
// =============================================================================

#[test]
fn old_receipt_verifies_under_old_epoch_not_new() {
    let n = 4;
    let threshold_u64 = 3u64;

    let (committee, members) = generate_test_committee(n, threshold_u64).unwrap();
    let kps = pk_vec(n);
    let ed_keys: Vec<PublicKey> = kps.iter().map(|(_, pk)| pk.clone()).collect();
    let fed_id_e0 = derive_federation_id_with_epoch(&ed_keys, 0);

    // Produce a receipt under epoch 0.
    let body = sample_body(77);
    let hash = body.body_hash();
    let shares: Vec<_> = members[..3]
        .iter()
        .map(|m| (m.index, committee.sign_share(m, &hash)))
        .collect();
    let qc = committee.aggregate(&shares, &hash).unwrap();
    let receipt = FederationReceipt::with_threshold_qc(fed_id_e0, 0, body, &qc);

    // Verifies at epoch 0.
    assert!(
        receipt.verify(Some(&committee), &ed_keys, 0, 0),
        "receipt must verify under the epoch 0 it was produced in"
    );

    // Does NOT verify if the caller expects epoch 1 (epoch binding check).
    assert!(
        !receipt.verify(Some(&committee), &ed_keys, 0, 1),
        "old receipt must not pass when verifier expects epoch 1"
    );
}

// =============================================================================
// Member ordering is irrelevant (deterministic sort inside Federation)
// =============================================================================

#[test]
fn member_order_independent_federation_id() {
    let kps = pk_vec(4);
    let pks: Vec<PublicKey> = kps.iter().map(|(_, pk)| pk.clone()).collect();

    // Two federations with the same keys in different order.
    let mut shuffled = pks.clone();
    shuffled.swap(0, 3);
    shuffled.swap(1, 2);

    let f1 = Federation::verifier_only(pks, 0, 3);
    let f2 = Federation::verifier_only(shuffled, 0, 3);

    assert_eq!(f1.id(), f2.id(), "federation_id must be order-independent");
}

// =============================================================================
// Member removal also produces a new id
// =============================================================================

#[test]
fn member_removal_changes_federation_id() {
    let kps = pk_vec(4);
    let pks: Vec<PublicKey> = kps.iter().map(|(_, pk)| pk.clone()).collect();

    let mut fed = Federation::verifier_only(pks.clone(), 0, 3);
    let id_4_members = fed.id();

    // Remove last member.
    let three_members: Vec<PublicKey> = pks[..3].to_vec();
    fed.apply_epoch_transition(three_members, 1, 2);

    assert_ne!(
        id_4_members,
        fed.id(),
        "removing a member must change the federation_id"
    );
}

// =============================================================================
// Old AttestedRoot verifies under old committee VK after epoch rotation
//
// This is the canonical backward-compatibility check: a receipt produced by
// the epoch-0 committee must still verify when the node has recorded both
// the epoch-0 and epoch-1 committees. Verification is keyed by
// (committee, epoch) so epoch 0 material always resolves to epoch 0 committee.
// =============================================================================

#[test]
fn old_attested_root_still_verifies_under_old_committee_vk() {
    let n = 4;
    let threshold_u64 = 3u64;

    // Epoch 0 committee
    let (committee_e0, members_e0) =
        generate_test_committee_with_seed(n, threshold_u64, [1u8; 32]).unwrap();
    let kps_e0 = pk_vec(n);
    let ed_e0: Vec<PublicKey> = kps_e0.iter().map(|(_, pk)| pk.clone()).collect();
    let fed_id_e0 = derive_federation_id_with_epoch(&ed_e0, 0);

    // Receipt produced by epoch-0 committee.
    let body = sample_body(99);
    let hash = body.body_hash();
    let shares: Vec<_> = members_e0[..3]
        .iter()
        .map(|m| (m.index, committee_e0.sign_share(m, &hash)))
        .collect();
    let qc_e0 = committee_e0.aggregate(&shares, &hash).unwrap();
    let old_receipt = FederationReceipt::with_threshold_qc(fed_id_e0, 0, body, &qc_e0);

    // Now the federation rotates to epoch 1 (different committee entirely).
    let (committee_e1, _members_e1) =
        generate_test_committee_with_seed(n, threshold_u64, [2u8; 32]).unwrap();
    let kps_e1 = pk_vec(n);
    let ed_e1: Vec<PublicKey> = kps_e1.iter().map(|(_, pk)| pk.clone()).collect();

    // Old receipt still verifies against epoch 0 committee and epoch 0 keys.
    assert!(
        old_receipt.verify(Some(&committee_e0), &ed_e0, 0, 0),
        "old receipt must remain verifiable against epoch-0 committee"
    );

    // Old receipt does NOT verify under epoch 1 material.
    assert!(
        !old_receipt.verify(Some(&committee_e1), &ed_e1, 0, 1),
        "old receipt must not verify under epoch-1 committee"
    );
}

// =============================================================================
// Votes (Ed25519) path: committee members sign; threshold met
// =============================================================================

#[test]
fn ed25519_votes_rotation_backward_compat() {
    let kps_e0 = pk_vec(4);
    let ed_e0: Vec<PublicKey> = kps_e0.iter().map(|(_, pk)| pk.clone()).collect();
    let fed_id_e0 = derive_federation_id_with_epoch(&ed_e0, 0);

    let body = sample_body(11);
    let hash = body.body_hash();

    // 3-of-4 sign at epoch 0.
    let votes: Vec<_> = kps_e0[..3]
        .iter()
        .map(|(sk, pk)| (pk.clone(), sign(sk, &hash)))
        .collect();

    let receipt = FederationReceipt::with_vote_signatures(fed_id_e0, 0, body.clone(), votes);

    // Verifies under epoch 0.
    assert!(receipt.verify(None, &ed_e0, 3, 0));

    // Does not verify if epoch expectation is 1.
    assert!(!receipt.verify(None, &ed_e0, 3, 1));

    // After rotation: epoch-1 federation has different keys → new fed_id.
    let kps_e1 = pk_vec(4);
    let ed_e1: Vec<PublicKey> = kps_e1.iter().map(|(_, pk)| pk.clone()).collect();

    // Old receipt over ed_e0 does not verify under ed_e1 keys (different id + different signers).
    assert!(
        !receipt.verify(None, &ed_e1, 3, 0),
        "epoch-0 receipt must not verify under epoch-1 member keys"
    );
}

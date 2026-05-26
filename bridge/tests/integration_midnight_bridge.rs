//! Integration test: Midnight bridge message validation, attestation signing,
//! and replay-deduplication behaviour.
//!
//! Covers:
//! - DreggToMidnight: self-consistency check (message hash matches payload)
//! - DreggToMidnight: forged/wrong pubkey attestation is rejected
//! - DreggToMidnight: tampered amount changes message hash → rejected
//! - MidnightToDregg: dedup_key uniqueness across tx_hash + log_index
//! - MidnightBridgeConfig: epoch key lookup returns correct key
//! - FederationAttestation: create + verify round-trip
//! - FederationAttestation: wrong pubkey rejects

use dregg_bridge::midnight::{
    DreggToMidnightMessage, EpochKey, FederationAttestation, MidnightBridgeConfig,
    MidnightToDreggMessage,
};
use ed25519_dalek::SigningKey;

// ============================================================================
// Helpers
// ============================================================================

fn signing_key(seed: u8) -> SigningKey {
    let secret = [seed; 32];
    SigningKey::from_bytes(&secret)
}

fn make_attestation(payload: &[u8], key: &SigningKey, epoch: u64) -> FederationAttestation {
    FederationAttestation::create(payload, key, epoch)
}

fn make_dregg_to_midnight(
    nullifier: [u8; 32],
    amount: u64,
    recipient: Vec<u8>,
    nonce: u64,
    sk: &SigningKey,
    epoch: u64,
) -> DreggToMidnightMessage {
    let msg_proto = DreggToMidnightMessage {
        nullifier,
        amount,
        midnight_recipient: recipient.clone(),
        attestation: FederationAttestation {
            message_hash: [0u8; 32],
            signature: vec![],
            epoch: 0,
            federation_pubkey: vec![],
        },
        nonce,
    };
    let payload = msg_proto.canonical_payload();
    let attestation = make_attestation(&payload, sk, epoch);
    DreggToMidnightMessage {
        nullifier,
        amount,
        midnight_recipient: recipient,
        attestation,
        nonce,
    }
}

// ============================================================================
// Test: DreggToMidnight self-consistency
// ============================================================================

#[test]
fn dregg_to_midnight_self_consistent() {
    let sk = signing_key(0x01);
    let msg = make_dregg_to_midnight([0x11; 32], 1_000, vec![0xAB; 32], 7, &sk, 1);
    assert!(
        msg.is_self_consistent(),
        "freshly created message must be self-consistent"
    );
}

// ============================================================================
// Test: tampered amount breaks self-consistency
// ============================================================================

#[test]
fn tampered_amount_breaks_self_consistency() {
    let sk = signing_key(0x02);
    let mut msg = make_dregg_to_midnight([0x22; 32], 500, vec![0xCC; 32], 3, &sk, 1);
    // Mutate the amount after attestation is created.
    msg.amount = 999_999;
    assert!(
        !msg.is_self_consistent(),
        "tampered amount must break self-consistency (message_hash no longer matches payload)"
    );
}

// ============================================================================
// Test: FederationAttestation verify round-trip
// ============================================================================

#[test]
fn attestation_verify_round_trip() {
    let sk = signing_key(0x03);
    let vk = sk.verifying_key();
    let payload = b"dregg bridge test payload";
    let att = FederationAttestation::create(payload, &sk, 42);

    assert!(
        att.verify(&vk.to_bytes()),
        "attestation must verify against the correct pubkey"
    );
}

// ============================================================================
// Test: attestation with wrong pubkey is rejected
// ============================================================================

#[test]
fn attestation_wrong_pubkey_rejected() {
    let sk1 = signing_key(0x04);
    let sk2 = signing_key(0x05);
    let vk2 = sk2.verifying_key();

    let payload = b"some bridge payload";
    let att = FederationAttestation::create(payload, &sk1, 1);

    // Verify against sk2's pubkey — must fail.
    assert!(
        !att.verify(&vk2.to_bytes()),
        "attestation signed by sk1 must not verify against vk2"
    );
}

// ============================================================================
// Test: attestation with invalid-length pubkey is rejected (no panic)
// ============================================================================

#[test]
fn attestation_short_pubkey_rejected() {
    let sk = signing_key(0x06);
    let payload = b"short pubkey test";
    let att = FederationAttestation::create(payload, &sk, 1);

    // 16-byte truncated pubkey — not a valid Ed25519 compressed point.
    let short = [0xAAu8; 16];
    assert!(
        !att.verify(&short),
        "short pubkey (16 bytes) must be rejected without panicking"
    );
}

// ============================================================================
// Test: MidnightToDregg dedup_key is (tx_hash, log_index)
// ============================================================================

#[test]
fn midnight_to_dregg_dedup_key() {
    let msg_a = MidnightToDreggMessage {
        midnight_tx_hash: [0x01; 32],
        amount: 100,
        dregg_recipient: [0xAA; 32],
        midnight_height: 500,
        log_index: 0,
    };
    let msg_b = MidnightToDreggMessage {
        midnight_tx_hash: [0x01; 32],
        amount: 200,                 // different amount
        dregg_recipient: [0xBB; 32], // different recipient
        midnight_height: 501,        // different height
        log_index: 0,                // SAME tx_hash + log_index
    };
    // Same tx_hash + log_index → same dedup key, regardless of other fields.
    assert_eq!(
        msg_a.dedup_key(),
        msg_b.dedup_key(),
        "messages with identical (tx_hash, log_index) must share a dedup key"
    );

    let msg_c = MidnightToDreggMessage {
        midnight_tx_hash: [0x01; 32],
        amount: 100,
        dregg_recipient: [0xAA; 32],
        midnight_height: 500,
        log_index: 1, // different log_index
    };
    assert_ne!(
        msg_a.dedup_key(),
        msg_c.dedup_key(),
        "messages with different log_index must have different dedup keys"
    );
}

// ============================================================================
// Test: MidnightBridgeConfig epoch key lookup
// ============================================================================

#[test]
fn epoch_key_lookup_returns_correct_key() {
    let key_epoch0 = [0xAA; 32];
    let key_epoch1 = [0xBB; 32];
    let key_current = [0xCC; 32];

    let config = MidnightBridgeConfig {
        contract_address: [0x00; 32],
        midnight_rpc_url: "ws://localhost:9944".into(),
        confirmations: 0,
        federation_keys: vec![
            EpochKey {
                from_epoch: 0,
                to_epoch: Some(0),
                pubkey: key_epoch0,
            },
            EpochKey {
                from_epoch: 1,
                to_epoch: Some(1),
                pubkey: key_epoch1,
            },
            EpochKey {
                from_epoch: 2,
                to_epoch: None,
                pubkey: key_current,
            },
        ],
        min_amount: 1,
        max_amount: 1_000_000,
    };

    assert_eq!(config.key_for_epoch(0), Some(&key_epoch0));
    assert_eq!(config.key_for_epoch(1), Some(&key_epoch1));
    assert_eq!(config.key_for_epoch(2), Some(&key_current));
    assert_eq!(config.key_for_epoch(999), Some(&key_current)); // unbounded
}

// ============================================================================
// Test: epoch key lookup returns None for uncovered epoch
// ============================================================================

#[test]
fn epoch_key_lookup_none_for_gap() {
    let config = MidnightBridgeConfig {
        contract_address: [0x00; 32],
        midnight_rpc_url: "ws://localhost:9944".into(),
        confirmations: 0,
        federation_keys: vec![EpochKey {
            from_epoch: 5,
            to_epoch: Some(10),
            pubkey: [0xAA; 32],
        }],
        min_amount: 1,
        max_amount: 1_000_000,
    };

    assert_eq!(
        config.key_for_epoch(0),
        None,
        "epoch 0 is before the key range"
    );
    assert_eq!(
        config.key_for_epoch(4),
        None,
        "epoch 4 is before the key range"
    );
    assert!(config.key_for_epoch(5).is_some());
    assert!(config.key_for_epoch(10).is_some());
    assert_eq!(
        config.key_for_epoch(11),
        None,
        "epoch 11 is after bounded range"
    );
}

// ============================================================================
// Test: canonical payload is deterministic
// ============================================================================

#[test]
fn dregg_to_midnight_canonical_payload_deterministic() {
    let msg = DreggToMidnightMessage {
        nullifier: [0x01; 32],
        amount: 12345,
        midnight_recipient: vec![0xAB; 32],
        attestation: FederationAttestation {
            message_hash: [0u8; 32],
            signature: vec![],
            epoch: 0,
            federation_pubkey: vec![],
        },
        nonce: 7,
    };

    let p1 = msg.canonical_payload();
    let p2 = msg.canonical_payload();
    assert_eq!(p1, p2, "canonical_payload must be deterministic");
    // Sanity: nullifier (32) + amount (8) + recipient (32) + nonce (8) = 80 bytes.
    assert_eq!(p1.len(), 80, "canonical payload must be exactly 80 bytes");
}

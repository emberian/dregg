//! Integration test: audit P0 #76 — the executor signature now binds
//! the *full* `receipt_hash`. Tampering any field that participates in
//! `receipt_hash()` must invalidate the signature.
//!
//! v2 narrowed the signed message to a turn-identity prefix; v3
//! widens it to the canonical receipt_hash so a signature cannot be
//! recovered onto a receipt with a tampered `was_encrypted`,
//! `finality`, `effects_hash`, `derivation_records`,
//! `previous_receipt_hash`, etc.

use dregg_turn::turn::{Finality, TurnReceipt};
use dregg_turn::verify::{sign_receipt, verify_receipt_chain_with_keys};
use dregg_types::CellId;
use ed25519_dalek::{SigningKey, VerifyingKey};

fn make_signing_key() -> SigningKey {
    SigningKey::from_bytes(&[7u8; 32])
}

fn base_receipt() -> TurnReceipt {
    TurnReceipt {
        turn_hash: [1u8; 32],
        forest_hash: [2u8; 32],
        pre_state_hash: [3u8; 32],
        post_state_hash: [4u8; 32],
        timestamp: 1000,
        effects_hash: [5u8; 32],
        computrons_used: 1234,
        action_count: 7,
        previous_receipt_hash: None,
        agent: CellId::from_bytes([9u8; 32]),
        federation_id: [10u8; 32],
        routing_directives: vec![],
        introduction_exports: vec![],
        derivation_records: vec![],
        emitted_events: vec![],
        executor_signature: None,
        finality: Finality::Final,
        was_encrypted: false,
        was_burn: false,
    }
}

fn signed(receipt: TurnReceipt, sk: &SigningKey) -> TurnReceipt {
    let mut r = receipt;
    let sk_bytes = sk.to_bytes();
    r.executor_signature = Some(sign_receipt(&r, &sk_bytes));
    r
}

#[test]
fn signature_roundtrip_v3_full_receipt_hash() {
    let sk = make_signing_key();
    let vk: VerifyingKey = sk.verifying_key();
    let pubkey = vk.to_bytes();

    let r = signed(base_receipt(), &sk);
    verify_receipt_chain_with_keys(&[r], &[pubkey]).expect("untampered receipt must verify");
}

#[test]
fn signature_rejects_tampered_was_encrypted() {
    let sk = make_signing_key();
    let pubkey = sk.verifying_key().to_bytes();

    let mut r = signed(base_receipt(), &sk);
    // Tamper a field that v2 did NOT cover but v3 does.
    r.was_encrypted = !r.was_encrypted;

    let err = verify_receipt_chain_with_keys(&[r], &[pubkey]);
    assert!(
        err.is_err(),
        "tampered was_encrypted must invalidate v3 sig"
    );
}

#[test]
fn signature_rejects_tampered_effects_hash() {
    let sk = make_signing_key();
    let pubkey = sk.verifying_key().to_bytes();

    let mut r = signed(base_receipt(), &sk);
    r.effects_hash = [0xEE; 32];

    let err = verify_receipt_chain_with_keys(&[r], &[pubkey]);
    assert!(err.is_err(), "tampered effects_hash must invalidate v3 sig");
}

#[test]
fn signature_rejects_tampered_finality() {
    let sk = make_signing_key();
    let pubkey = sk.verifying_key().to_bytes();

    let mut r = signed(base_receipt(), &sk);
    r.finality = Finality::Tentative;

    let err = verify_receipt_chain_with_keys(&[r], &[pubkey]);
    assert!(err.is_err(), "tampered finality must invalidate v3 sig");
}

#[test]
fn signature_rejects_tampered_computrons() {
    let sk = make_signing_key();
    let pubkey = sk.verifying_key().to_bytes();

    let mut r = signed(base_receipt(), &sk);
    r.computrons_used = r.computrons_used.wrapping_add(1);

    let err = verify_receipt_chain_with_keys(&[r], &[pubkey]);
    assert!(
        err.is_err(),
        "tampered computrons_used must invalidate v3 sig"
    );
}

#[test]
fn signature_rejects_tampered_previous_receipt_hash() {
    let sk = make_signing_key();
    let pubkey = sk.verifying_key().to_bytes();

    let mut r = signed(base_receipt(), &sk);
    r.previous_receipt_hash = Some([0xBE; 32]);

    let err = verify_receipt_chain_with_keys(&[r], &[pubkey]);
    assert!(
        err.is_err(),
        "tampered previous_receipt_hash must invalidate v3 sig"
    );
}

#[test]
fn v2_canonical_message_is_still_recoverable() {
    // The v2 narrow message is preserved as a separate accessor for
    // fixtures and legacy verifiers. It is shorter than the v3 message
    // and uses a different domain string, so a v3 signature cannot be
    // confused for a v2 signature and vice versa.
    let r = base_receipt();
    let v2 = r.canonical_executor_signed_message_v2();
    let v3 = r.canonical_executor_signed_message();
    assert_ne!(v2, v3);
    assert!(v2.starts_with(b"executor-receipt-sig-v2:"));
    assert!(v3.starts_with(b"executor-receipt-sig-v3:"));
}

//! Integration test: encrypted-turn submission (audit-privacy.md §11.2).
//!
//! Exercises the same executor code path as `POST /turns/submit-encrypted`
//! without an HTTP server. The key invariants tested are:
//!
//!   1. `apply_encrypted_turn` with the correct sealer key → committed,
//!      `was_encrypted = true`.
//!   2. The sealer secret is derived from the cipherclerk the same way the
//!      node handler does it (domain `"dregg-turn-unsealer-v1"`).
//!   3. Forged sealer secret → rejected.
//!   4. Malformed postcard body (simulating a bad HTTP body) → deserialization
//!      error, not panic.

use dregg_cell::{Cell, CellId, Ledger};
use dregg_sdk::AgentCipherclerk;
use dregg_turn::{ActionBuilder, CallForest, ComputronCosts, Turn, TurnExecutor};
use zeroize::Zeroizing;

/// The same domain string used by the node handler to derive the unsealer.
const TURN_UNSEALER_DOMAIN: &str = "dregg-turn-unsealer-v1";

// ---------------------------------------------------------------------------
// Helper
// ---------------------------------------------------------------------------

fn test_key(label: &str) -> [u8; 32] {
    *blake3::hash(format!("node-encrypted-test:{label}").as_bytes()).as_bytes()
}

fn make_cclerk(label: &str) -> AgentCipherclerk {
    AgentCipherclerk::from_key_bytes(Zeroizing::new(test_key(label)))
}

fn make_ledger(cclerk: &AgentCipherclerk) -> Ledger {
    let mut ledger = Ledger::new();
    let cell = Cell::with_balance(cclerk.public_key().0, [0u8; 32], 1_000_000);
    ledger
        .insert_cell(cell)
        .expect("test cell insert must succeed");
    ledger
}

fn valid_turn(agent: CellId, nonce: u64) -> Turn {
    let mut call_forest = CallForest::new();
    call_forest.add_root(
        ActionBuilder::new_unchecked_for_tests(agent, "encrypted_submit_noop", agent).build(),
    );

    Turn {
        agent,
        nonce,
        fee: 100,
        memo: None,
        valid_until: None,
        call_forest,
        depends_on: vec![],
        previous_receipt_hash: None,
        conservation_proof: None,
        sovereign_witnesses: Default::default(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: vec![],
        cross_effect_dependencies: vec![],
        effect_witness_index_map: vec![],
    }
}

// ---------------------------------------------------------------------------
// 1. Correct sealer secret (derived from cipherclerk) → accepted
// ---------------------------------------------------------------------------

/// Derive the executor X25519 unsealer secret from the node's cipherclerk
/// via `derive_symmetric_key("dregg-turn-unsealer-v1")` — exactly what the
/// production handler does — and verify that the encrypted-turn roundtrip
/// succeeds with `was_encrypted = true`.
#[test]
fn encrypted_turn_with_node_derived_sealer_commits() {
    let executor_cclerk = make_cclerk("node-executor");

    // The node derives the X25519 secret from its own cipherclerk.
    let sealer_secret = executor_cclerk.derive_symmetric_key(TURN_UNSEALER_DOMAIN);
    let sealer_public = {
        let pk = x25519_dalek::PublicKey::from(&x25519_dalek::StaticSecret::from(sealer_secret));
        *pk.as_bytes()
    };

    // The sender (using their own cipherclerk) encrypts to the executor's public key.
    let sender_cclerk = make_cclerk("sender");
    let agent = {
        let raw = dregg_cell::CellId::derive_raw(&sender_cclerk.public_key().0, &[0u8; 32]);
        CellId(raw.0)
    };
    let turn = valid_turn(agent, 0);
    let encrypted = sender_cclerk
        .make_encrypted_turn(&turn, &sealer_public, 0)
        .expect("make_encrypted_turn must succeed");

    // The executor decrypts + applies.
    let executor = TurnExecutor::new(ComputronCosts::default());
    let mut ledger = make_ledger(&sender_cclerk);
    let receipt = executor
        .apply_encrypted_turn(&encrypted, &sealer_secret, &mut ledger)
        .expect("apply_encrypted_turn with correct sealer must succeed");

    assert!(
        receipt.was_encrypted,
        "receipt.was_encrypted must be true on the encrypted path"
    );
    assert_eq!(
        receipt.agent, agent,
        "receipt agent must match the turn agent"
    );
}

// ---------------------------------------------------------------------------
// 2. Forged sealer secret → rejected
// ---------------------------------------------------------------------------

/// An attacker who doesn't know the executor's unsealer secret encrypts to
/// a *different* public key. The executor's `apply_encrypted_turn` must
/// return an error.
#[test]
fn encrypted_turn_with_forged_sealer_is_rejected() {
    // Attacker generates their own X25519 keypair.
    let mut attacker_secret = [0u8; 32];
    attacker_secret.copy_from_slice(blake3::hash(b"attacker-x25519-secret").as_bytes());
    let attacker_public = {
        let pk = x25519_dalek::PublicKey::from(&x25519_dalek::StaticSecret::from(attacker_secret));
        *pk.as_bytes()
    };

    // Real executor's secret (unknown to attacker).
    let executor_cclerk = make_cclerk("executor-forged");
    let real_sealer_secret = executor_cclerk.derive_symmetric_key(TURN_UNSEALER_DOMAIN);
    assert_ne!(
        real_sealer_secret, attacker_secret,
        "secrets must differ for the test to be meaningful"
    );

    // Sender encrypts to the attacker's public key instead of the executor's.
    let sender_cclerk = make_cclerk("sender-forged");
    let agent = {
        let raw = dregg_cell::CellId::derive_raw(&sender_cclerk.public_key().0, &[0u8; 32]);
        CellId(raw.0)
    };
    let turn = valid_turn(agent, 0);
    let encrypted = sender_cclerk
        .make_encrypted_turn(&turn, &attacker_public, 0)
        .expect("encryption itself must succeed");

    // The executor tries to decrypt with its own (real) secret → must fail.
    let executor = TurnExecutor::new(ComputronCosts::default());
    let mut ledger = make_ledger(&sender_cclerk);
    let result = executor.apply_encrypted_turn(&encrypted, &real_sealer_secret, &mut ledger);
    assert!(
        result.is_err(),
        "apply_encrypted_turn with wrong sealer must return an error; got: {:?}",
        result
    );
}

// ---------------------------------------------------------------------------
// 3. Malformed postcard body → deserialization error (not panic)
// ---------------------------------------------------------------------------

/// The production handler calls `postcard::from_bytes(&body)` and returns
/// 400 on failure. Here we verify the postcard side directly: garbage bytes
/// must produce a deserialization error.
#[test]
fn malformed_postcard_body_deserialize_fails_gracefully() {
    let garbage = b"this is not a valid postcard-encoded EncryptedTurn";
    let result: Result<dregg_turn::EncryptedTurn, _> = postcard::from_bytes(garbage);
    assert!(
        result.is_err(),
        "postcard::from_bytes must return Err on garbage input"
    );
}

// ---------------------------------------------------------------------------
// 4. Encrypted turn: was_encrypted is bound into receipt_hash
// ---------------------------------------------------------------------------

/// Because `receipt_hash()` includes the `was_encrypted` flag, two receipts
/// that differ only in `was_encrypted` must have different hashes. This
/// ensures a malicious executor cannot strip the flag post-commit.
#[test]
fn was_encrypted_flag_is_bound_into_receipt_hash() {
    let executor_cclerk = make_cclerk("hash-binding-executor");
    let sealer_secret = executor_cclerk.derive_symmetric_key(TURN_UNSEALER_DOMAIN);
    let sealer_public = {
        let pk = x25519_dalek::PublicKey::from(&x25519_dalek::StaticSecret::from(sealer_secret));
        *pk.as_bytes()
    };

    let sender_cclerk = make_cclerk("hash-binding-sender");
    let agent = {
        let raw = dregg_cell::CellId::derive_raw(&sender_cclerk.public_key().0, &[0u8; 32]);
        CellId(raw.0)
    };
    let turn = valid_turn(agent, 0);
    let encrypted = sender_cclerk
        .make_encrypted_turn(&turn, &sealer_public, 0)
        .expect("encryption must succeed");

    let executor = TurnExecutor::new(ComputronCosts::default());
    let mut ledger = make_ledger(&sender_cclerk);
    let mut receipt = executor
        .apply_encrypted_turn(&encrypted, &sealer_secret, &mut ledger)
        .expect("apply must succeed");

    assert!(receipt.was_encrypted);
    let hash_encrypted = receipt.receipt_hash();

    // Flip the flag and recompute — the hash must differ.
    receipt.was_encrypted = false;
    let hash_cleartext = receipt.receipt_hash();

    assert_ne!(
        hash_encrypted, hash_cleartext,
        "was_encrypted must be bound into receipt_hash; \
         flipping the flag must change the hash"
    );
}

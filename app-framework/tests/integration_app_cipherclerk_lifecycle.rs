//! Integration test: AppCipherclerk + EmbeddedExecutor full lifecycle.
//!
//! Drives the full "construct → sign turn → submit → verify receipt → restart"
//! flow:
//!
//! 1. Construct AppCipherclerk + EmbeddedExecutor.
//! 2. Build and sign an action.
//! 3. Submit via EmbeddedExecutor; receive a TurnReceipt.
//! 4. Verify receipt is non-trivial (non-zero turn_hash, correct agent, action_count).
//! 5. Submit a second turn; verify receipt chain advances (previous_receipt_hash grows).
//! 6. Reconstruct a second AppCipherclerk sharing the same underlying cipherclerk
//!    (the "restart from state" path); verify it produces the same cell_id and
//!    consistent public_key.
//! 7. Multi-action atomic turn: two independent actions bundled; verify both roots
//!    appear in the same receipt.
//! 8. Federation-id binding: two cipherclerks with different federation_ids must
//!    produce different signatures for the same (target, method, effects) triple.

use pyana_app_framework::{AgentCipherclerk, AppCipherclerk, CellId, EmbeddedExecutor};
use pyana_turn::action::Authorization;

// ── helpers ─────────────────────────────────────────────────────────────────

fn make_cclerk(federation_id: [u8; 32]) -> AppCipherclerk {
    AppCipherclerk::new(AgentCipherclerk::new(), federation_id)
}

fn make_executor(cclerk: &AppCipherclerk) -> EmbeddedExecutor {
    EmbeddedExecutor::new(cclerk, "default")
}

fn target_cell() -> CellId {
    CellId::from_bytes([3u8; 32])
}

// ── tests ────────────────────────────────────────────────────────────────────

#[test]
fn construct_sign_submit_receipt() {
    let cclerk = make_cclerk([1u8; 32]);
    let executor = make_executor(&cclerk);

    let action = cclerk.make_self_action("noop", vec![]);
    let receipt = executor
        .submit_action(&cclerk, action)
        .expect("submit must succeed");

    // Receipt must have a non-zero turn_hash.
    assert_ne!(receipt.turn_hash, [0u8; 32], "turn_hash must be non-zero");
    // Agent must match the cclerk's cell_id.
    assert_eq!(
        receipt.agent,
        cclerk.cell_id(),
        "receipt agent must match cclerk cell_id"
    );
    // One action in the forest.
    assert_eq!(
        receipt.action_count, 1,
        "single-action turn must have action_count == 1"
    );
}

#[test]
fn consecutive_turns_receipt_chain_advances() {
    let cclerk = make_cclerk([2u8; 32]);
    let executor = make_executor(&cclerk);

    let a1 = cclerk.make_self_action("step-1", vec![]);
    let r1 = executor
        .submit_action(&cclerk, a1)
        .expect("first submit must succeed");

    let a2 = cclerk.make_self_action("step-2", vec![]);
    let r2 = executor
        .submit_action(&cclerk, a2)
        .expect("second submit must succeed");

    // Second receipt must have a previous_receipt_hash (chain grows).
    assert!(
        r2.previous_receipt_hash.is_some(),
        "second receipt must carry previous_receipt_hash"
    );

    // The previous_receipt_hash of receipt #2 must equal the receipt_hash of receipt #1.
    assert_eq!(
        r2.previous_receipt_hash,
        Some(r1.receipt_hash()),
        "previous_receipt_hash must chain to prior receipt_hash"
    );

    // Turn hashes are distinct (different nonces / actions).
    assert_ne!(
        r1.turn_hash, r2.turn_hash,
        "consecutive turns must produce distinct turn_hashes"
    );
}

#[test]
fn shared_cclerk_same_cell_id_after_restart() {
    // "Restart from state": a second AppCipherclerk built from the same
    // underlying shared AgentCipherclerk handle (as returned by
    // shared_cipherclerk()) must produce the same cell_id and public_key.
    let original = make_cclerk([5u8; 32]);

    let shared = original.shared_cipherclerk();
    let restarted = AppCipherclerk::from_shared(shared, [5u8; 32]);

    assert_eq!(
        original.cell_id(),
        restarted.cell_id(),
        "restarted cclerk must have the same cell_id as the original"
    );
    assert_eq!(
        original.public_key(),
        restarted.public_key(),
        "restarted cclerk must have the same public_key"
    );
}

#[test]
fn restarted_executor_can_submit_after_original_turns() {
    // Build first executor, submit a turn, then construct a second executor
    // sharing the same cclerk. The second executor must successfully accept
    // another turn (the receipt chain is alive in the shared cclerk).
    let cclerk = make_cclerk([6u8; 32]);
    let exec1 = make_executor(&cclerk);

    let a1 = cclerk.make_self_action("first", vec![]);
    exec1
        .submit_action(&cclerk, a1)
        .expect("first submit must succeed");

    // Second executor sharing same cclerk.
    let exec2 = EmbeddedExecutor::new(&cclerk, "default");
    let a2 = cclerk.make_self_action("after-restart", vec![]);
    let r2 = exec2
        .submit_action(&cclerk, a2)
        .expect("post-restart submit must succeed");

    // Receipt must have a previous_receipt_hash, proving chain continuity.
    assert!(
        r2.previous_receipt_hash.is_some(),
        "post-restart receipt must carry previous_receipt_hash"
    );
}

#[test]
fn multi_action_atomic_turn_both_roots_in_receipt() {
    let cclerk = make_cclerk([7u8; 32]);
    let executor = make_executor(&cclerk);

    let a1 = cclerk.make_self_action("first-action", vec![]);
    let a2 = cclerk.make_self_action("second-action", vec![]);

    let turn = cclerk.make_turn_with_actions(vec![a1, a2]);
    let receipt = executor
        .submit_turn(&turn)
        .expect("multi-action turn must succeed");

    // Both actions are in the same turn forest → action_count == 2.
    assert_eq!(
        receipt.action_count, 2,
        "multi-action turn must report action_count == 2"
    );
    assert_ne!(receipt.turn_hash, [0u8; 32], "turn_hash must be non-zero");
}

#[test]
fn different_federation_ids_produce_different_signatures() {
    // Two cipherclerks with different federation_ids must produce
    // different signatures for the same logical action, preventing cross-
    // federation replay.
    let fed_a = AppCipherclerk::new(AgentCipherclerk::new(), [10u8; 32]);
    // Clone the underlying SDK cclerk so both handles share the same identity
    // (same signing key). Only the federation_id differs.
    let shared = fed_a.shared_cipherclerk();
    let fed_b = AppCipherclerk::from_shared(shared, [20u8; 32]);

    let target = target_cell();
    let action_a = fed_a.make_action(target, "ping", vec![]);
    let action_b = fed_b.make_action(target, "ping", vec![]);

    let sig_a = match action_a.authorization {
        Authorization::Signature(a, b) => (a, b),
        other => panic!("expected Signature, got {other:?}"),
    };
    let sig_b = match action_b.authorization {
        Authorization::Signature(a, b) => (a, b),
        other => panic!("expected Signature, got {other:?}"),
    };

    // Signatures must differ (different federation_id → different signing message).
    assert_ne!(
        sig_a, sig_b,
        "different federation_ids must produce different signatures"
    );
}

#[test]
fn make_self_action_targets_cclerk_own_cell() {
    let cclerk = make_cclerk([8u8; 32]);
    let action = cclerk.make_self_action("heartbeat", vec![]);

    assert_eq!(
        action.target,
        cclerk.cell_id(),
        "make_self_action must target the cclerk's own cell"
    );
    // Must carry a real signature.
    match action.authorization {
        Authorization::Signature(a, b) => {
            assert!(
                a != [0u8; 32] || b != [0u8; 32],
                "signature must be non-zero"
            );
        }
        other => panic!("expected Signature, got {other:?}"),
    }
}

#[test]
fn domain_variant_produces_distinct_cell_id() {
    // AppCipherclerk::with_domain("x") must produce a different cell_id
    // than the default domain — so per-domain cells are distinct.
    let base = make_cclerk([9u8; 32]);
    let alt = base.clone().with_domain("storage");

    assert_ne!(
        base.cell_id(),
        alt.cell_id(),
        "different domains must produce different cell_ids"
    );
    // But the public_key (signing identity) is the same.
    assert_eq!(
        base.public_key(),
        alt.public_key(),
        "domain change must not change public_key"
    );
}

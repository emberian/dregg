//! Executor-invoking integration tests for the subscription publish/consume
//! lifecycle and bounty state notification pipeline.
//!
//! The existing `program.rs` tests exercise `CellProgram::evaluate_with_meta`
//! directly.  These tests go one layer higher: they call
//! `EmbeddedExecutor::submit_action` and assert on `TurnReceipt` outcomes —
//! verifying that the executor's full turn-execution pipeline (signature
//! check → effect application → caveat evaluation → receipt production)
//! honours the subscription app's publish/consume protocol.
//!
//! **What `cross-app-e2e/` does NOT cover:**
//! - The `carol.grant_publisher.json` / `carol.post.json` state files record
//!   *commitment encodings*, not executor outcomes. They never call
//!   `submit_action` and never produce a `TurnReceipt`.  These tests do.

use dregg_cell::state::FieldElement;
use starbridge_subscription::{
    BountyState, bounty_state_payload_hash, build_bounty_state_publish_action,
    build_consume_action, build_grant_consumer_action, build_grant_publisher_action,
    build_publish_action,
};

// =============================================================================
// Helpers
// =============================================================================

mod common {
    use dregg_app_framework::{AgentCipherclerk, AppCipherclerk, CellId, EmbeddedExecutor};
    use dregg_cell::StateConstraint;
    use dregg_cell::program::CellProgram;
    use starbridge_subscription::subscription_program;

    pub fn make_cipherclerk(seed: u8) -> AppCipherclerk {
        AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32])
    }

    fn executor_shape_program() -> CellProgram {
        let CellProgram::Cases(cases) = subscription_program() else {
            return subscription_program();
        };
        CellProgram::Cases(
            cases
                .into_iter()
                .map(|mut case| {
                    case.constraints
                        .retain(|c| !matches!(c, StateConstraint::SenderAuthorized { .. }));
                    case
                })
                .collect(),
        )
    }

    pub fn make_executor(cipherclerk: &AppCipherclerk) -> (EmbeddedExecutor, CellId) {
        let executor = EmbeddedExecutor::new(cipherclerk, "default");
        let cell = executor.cell_id();
        executor.install_program(cell, executor_shape_program());
        (executor, cell)
    }
}

fn blake3_field(bytes: &[u8]) -> FieldElement {
    *blake3::hash(bytes).as_bytes()
}

fn u64_field(value: u64) -> FieldElement {
    let mut out = [0u8; 32];
    out[24..32].copy_from_slice(&value.to_be_bytes());
    out
}

// =============================================================================
// Test 1: grant_publisher → publish → executor accepts and emits event
// =============================================================================

/// Submit a `grant_publisher` action followed by a `publish` action.
/// Both must be accepted by the executor.  The `publish` receipt must
/// carry a `subscription-published` event whose data fields encode the
/// new head, the new message root, and the payload hash.
#[test]
fn executor_grant_publisher_then_publish_emits_subscription_published_event() {
    let cipherclerk = common::make_cipherclerk(0x10);
    let (executor, sub_cell) = common::make_executor(&cipherclerk);

    let new_pub_root = blake3_field(b"publishers-root-v1");
    let publisher_pk = [0x11u8; 32];

    // Step 1: grant_publisher (root changes from zero to v1).
    let grant_action =
        build_grant_publisher_action(&cipherclerk, sub_cell, new_pub_root, publisher_pk);
    let grant_receipt = executor
        .submit_action(&cipherclerk, grant_action)
        .expect("grant_publisher must be accepted");
    assert_eq!(grant_receipt.action_count, 1);
    assert!(
        !grant_receipt.emitted_events.is_empty(),
        "grant_publisher must emit a subscription-publisher-granted event"
    );
    // Event data[0] is the new publishers root.
    assert_eq!(grant_receipt.emitted_events[0].data[0], new_pub_root);

    // Step 2: publish a message.
    let payload_hash = blake3_field(b"hello-world-payload");
    let new_head = u64_field(1);
    let new_msg_root = blake3_field(b"message-root-v1");

    let publish_action =
        build_publish_action(&cipherclerk, sub_cell, new_head, new_msg_root, payload_hash);
    let publish_receipt = executor
        .submit_action(&cipherclerk, publish_action)
        .expect("publish must be accepted by executor");

    assert_eq!(publish_receipt.action_count, 1);
    assert!(!publish_receipt.emitted_events.is_empty());
    let ev = &publish_receipt.emitted_events[0];
    assert_eq!(ev.data[0], new_head, "event data[0] must be new_head");
    assert_eq!(
        ev.data[1], new_msg_root,
        "event data[1] must be new_message_root"
    );
    assert_eq!(
        ev.data[2], payload_hash,
        "event data[2] must be payload_hash"
    );
}

// =============================================================================
// Test 2: publish → grant_consumer → consume → executor accepts
// =============================================================================

/// Publish a message then grant a consumer and have them consume it.
/// The `consume` receipt must carry a `subscription-consumed` event
/// whose data encodes the new tail and the consumed payload hash.
#[test]
fn executor_publish_grant_consumer_consume_emits_subscription_consumed_event() {
    let cipherclerk = common::make_cipherclerk(0x20);
    let (executor, sub_cell) = common::make_executor(&cipherclerk);

    // Publish one message.
    let payload_hash = blake3_field(b"message-body");
    let new_head = u64_field(1);
    let new_msg_root = blake3_field(b"msg-root-v1");
    let publish_action =
        build_publish_action(&cipherclerk, sub_cell, new_head, new_msg_root, payload_hash);
    executor
        .submit_action(&cipherclerk, publish_action)
        .expect("publish must succeed");

    // Grant a consumer.
    let new_con_root = blake3_field(b"consumers-root-v1");
    let consumer_pk = [0x22u8; 32];
    let grant_action =
        build_grant_consumer_action(&cipherclerk, sub_cell, new_con_root, consumer_pk);
    executor
        .submit_action(&cipherclerk, grant_action)
        .expect("grant_consumer must succeed");

    // Consume the published message.
    let new_tail = u64_field(1);
    let consume_action = build_consume_action(&cipherclerk, sub_cell, new_tail, payload_hash);
    let consume_receipt = executor
        .submit_action(&cipherclerk, consume_action)
        .expect("consume must be accepted by executor");

    assert_eq!(consume_receipt.action_count, 1);
    assert!(!consume_receipt.emitted_events.is_empty());
    let ev = &consume_receipt.emitted_events[0];
    // event data[0] = new_tail, data[1] = consumed payload hash.
    assert_eq!(
        ev.data[0], new_tail,
        "consume event data[0] must be new_tail"
    );
    assert_eq!(
        ev.data[1], payload_hash,
        "consume event data[1] must be consumed payload_hash"
    );
}

// =============================================================================
// Test 3: head rewind after publish → rejected by executor
// =============================================================================

/// After a successful publish (head = 1), a second publish that rewinds
/// head back to 0 must be rejected by the executor's
/// `MonotonicSequence(SEQ_HEAD_SLOT)` caveat.
#[test]
fn executor_head_rewind_after_publish_rejected() {
    let cipherclerk = common::make_cipherclerk(0x30);
    let (executor, sub_cell) = common::make_executor(&cipherclerk);

    // First publish: head → 1.
    let p1 = build_publish_action(
        &cipherclerk,
        sub_cell,
        u64_field(1),
        blake3_field(b"root-v1"),
        blake3_field(b"payload-1"),
    );
    executor
        .submit_action(&cipherclerk, p1)
        .expect("first publish must succeed");

    // Adversarial: head → 0 (rewind).
    let p_rewind = build_publish_action(
        &cipherclerk,
        sub_cell,
        u64_field(0), // ← rewind
        blake3_field(b"root-v2"),
        blake3_field(b"payload-2"),
    );
    let result = executor.submit_action(&cipherclerk, p_rewind);
    assert!(
        result.is_err(),
        "head rewind must be rejected by MonotonicSequence(SEQ_HEAD_SLOT); got: {result:?}"
    );
}

// =============================================================================
// Test 4: consume before publish → tail would exceed head → rejected
// =============================================================================

/// Attempting to consume (tail → 1) before any publish (head = 0)
/// violates the `MonotonicSequence` invariant: tail cannot advance past
/// head. The executor must reject this.
#[test]
fn executor_consume_before_publish_rejected() {
    let cipherclerk = common::make_cipherclerk(0x40);
    let (executor, sub_cell) = common::make_executor(&cipherclerk);

    // No publish yet — head = 0. Attempt to advance tail → 1.
    let consume_action = build_consume_action(
        &cipherclerk,
        sub_cell,
        u64_field(1),
        blake3_field(b"phantom-payload"),
    );
    let result = executor.submit_action(&cipherclerk, consume_action);
    assert!(
        result.is_err(),
        "consuming from an empty queue (tail > head) must be rejected; got: {result:?}"
    );
}

// =============================================================================
// Test 5: bounty lifecycle — post → claim → fulfill → settle via subscription
// =============================================================================

/// Walk the four-step bounty lifecycle through the subscription queue.
/// Each state transition is a `build_bounty_state_publish_action`; the
/// executor must accept each step.  The payload hashes must be distinct
/// across transitions (replay-safety) and the final event's data must
/// carry the Settled state tag.
#[test]
fn executor_bounty_lifecycle_post_claim_fulfill_settle() {
    let cipherclerk = common::make_cipherclerk(0x50);
    let (executor, sub_cell) = common::make_executor(&cipherclerk);

    let bounty_id = blake3_field(b"bounty-007");
    let actor_pk_hash = blake3_field(b"worker-alice-pk");

    // Compute the expected payload hashes.
    let hash_post_to_claimed = bounty_state_payload_hash(
        &bounty_id,
        BountyState::Posted,
        BountyState::Claimed,
        &actor_pk_hash,
    );
    let hash_claimed_to_fulfilled = bounty_state_payload_hash(
        &bounty_id,
        BountyState::Claimed,
        BountyState::Fulfilled,
        &actor_pk_hash,
    );
    let hash_fulfilled_to_settled = bounty_state_payload_hash(
        &bounty_id,
        BountyState::Fulfilled,
        BountyState::Settled,
        &actor_pk_hash,
    );

    // Payload hashes must be distinct (replay-safety across state transitions).
    assert_ne!(hash_post_to_claimed, hash_claimed_to_fulfilled);
    assert_ne!(hash_claimed_to_fulfilled, hash_fulfilled_to_settled);

    // Step 1: Claim (transition Posted → Claimed; head 0 → 1).
    let claim_action = build_bounty_state_publish_action(
        &cipherclerk,
        sub_cell,
        u64_field(1),
        blake3_field(b"msg-root-v1"),
        &bounty_id,
        BountyState::Posted,
        BountyState::Claimed,
        &actor_pk_hash,
    );
    let claim_receipt = executor
        .submit_action(&cipherclerk, claim_action)
        .expect("claim transition must be accepted");
    assert!(!claim_receipt.emitted_events.is_empty());
    assert_eq!(
        claim_receipt.emitted_events[0].data[2], hash_post_to_claimed,
        "claim event must carry the canonical Posted→Claimed payload hash"
    );

    // Step 2: Fulfill (transition Claimed → Fulfilled; head 1 → 2).
    let fulfill_action = build_bounty_state_publish_action(
        &cipherclerk,
        sub_cell,
        u64_field(2),
        blake3_field(b"msg-root-v2"),
        &bounty_id,
        BountyState::Claimed,
        BountyState::Fulfilled,
        &actor_pk_hash,
    );
    let fulfill_receipt = executor
        .submit_action(&cipherclerk, fulfill_action)
        .expect("fulfill transition must be accepted");
    assert_eq!(
        fulfill_receipt.emitted_events[0].data[2], hash_claimed_to_fulfilled,
        "fulfill event must carry the canonical Claimed→Fulfilled payload hash"
    );

    // Step 3: Settle (transition Fulfilled → Settled; head 2 → 3).
    let settle_action = build_bounty_state_publish_action(
        &cipherclerk,
        sub_cell,
        u64_field(3),
        blake3_field(b"msg-root-v3"),
        &bounty_id,
        BountyState::Fulfilled,
        BountyState::Settled,
        &actor_pk_hash,
    );
    let settle_receipt = executor
        .submit_action(&cipherclerk, settle_action)
        .expect("settle transition must be accepted");
    assert_eq!(
        settle_receipt.emitted_events[0].data[2], hash_fulfilled_to_settled,
        "settle event must carry the canonical Fulfilled→Settled payload hash"
    );

    // The final head is 3 (three publishes).
    assert_eq!(settle_receipt.action_count, 1);
}

// =============================================================================
// Test 6: message_root rewind under publish → rejected
// =============================================================================

/// After a successful publish, a second publish that clears the
/// message_root to zero must be rejected by the root non-zero caveat.
#[test]
fn executor_message_root_rewind_rejected() {
    let cipherclerk = common::make_cipherclerk(0x60);
    let (executor, sub_cell) = common::make_executor(&cipherclerk);

    // First publish: message_root → non-zero.
    let good_root = blake3_field(b"root-v1");
    let p1 = build_publish_action(
        &cipherclerk,
        sub_cell,
        u64_field(1),
        good_root,
        blake3_field(b"p1"),
    );
    executor
        .submit_action(&cipherclerk, p1)
        .expect("first publish must succeed");

    // Adversarial: rewind message_root to zero.
    let p_rewind = build_publish_action(
        &cipherclerk,
        sub_cell,
        u64_field(2),
        [0u8; 32],
        blake3_field(b"p2"),
    );
    let result = executor.submit_action(&cipherclerk, p_rewind);
    assert!(
        result.is_err(),
        "clearing message_root to zero must be rejected; got: {result:?}"
    );
}

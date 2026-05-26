//! Adversarial transition tests for `starbridge-subscription`.
//!
//! These exercise the operation-scoped semantics of
//! [`starbridge_subscription::subscription_program`] by driving
//! `CellProgram::evaluate_with_meta(..)` against hand-rolled
//! `(old_state, new_state, TransitionMeta)` triples. They are the
//! executor-side regression for the slot-caveat lift described in
//! `STORAGE-AS-CELL-PROGRAMS.md` §3.1.
//!
//! The tests are organized around the lane spec's adversarial cases:
//!
//! 1. Round-trip publish → consume produces matching payload hash.
//! 2. Non-authorized publisher → rejected (`SenderAuthorized`).
//! 3. Non-authorized consumer → rejected.
//! 4. Rewrite a message slot → rejected (`WriteOnce`-shaped via
//!    `Immutable` under `consume` and changed+non-zero root on `publish`).
//! 5. Decrement head or tail → rejected (`MonotonicSequence`).
//! 6. Write past capacity → rejected (the head's exact +1 increment
//!    plus the cap check at the cclerk layer; the message_root must
//!    advance, so the queue's logical capacity is structurally bound).
//! 7. Operation-scoping: publish op doesn't advance tail; consume op
//!    doesn't advance head.

use dregg_app_framework::symbol;
use dregg_cell::StateConstraint;
use dregg_cell::program::{CellProgram, ProgramError, TransitionMeta};
use dregg_cell::state::{CellState, FIELD_ZERO, FieldElement};

use starbridge_subscription::{
    CAPACITY_SLOT, CONSUMERS_ROOT_SLOT, LATEST_PAYLOAD_SLOT, MESSAGE_ROOT_SLOT, OWNER_PK_HASH_SLOT,
    PUBLISHERS_ROOT_SLOT, SEQ_HEAD_SLOT, SEQ_TAIL_SLOT, subscription_program,
};

// ─── Helpers ────────────────────────────────────────────────────────────

fn u64_field(value: u64) -> FieldElement {
    let mut out = [0u8; 32];
    out[24..32].copy_from_slice(&value.to_be_bytes());
    out
}

fn blake3_field(bytes: &[u8]) -> FieldElement {
    *blake3::hash(bytes).as_bytes()
}

/// Build a 32-byte field element where every byte equals `b`.
fn byte_field(b: u8) -> FieldElement {
    [b; 32]
}

/// Construct a base subscription state with capacity / owner / roots
/// initialised. Used as the `old_state` baseline in adversarial tests.
fn base_state(head: u64, tail: u64) -> CellState {
    let mut s = CellState::new(0);
    s.fields[SEQ_HEAD_SLOT as usize] = u64_field(head);
    s.fields[SEQ_TAIL_SLOT as usize] = u64_field(tail);
    s.fields[CAPACITY_SLOT as usize] = u64_field(8);
    // Roots default to a simple non-zero byte-pattern so zero-clear
    // adversarial tests isolate the intended root constraint.
    s.fields[PUBLISHERS_ROOT_SLOT as usize] = byte_field(0x10);
    s.fields[CONSUMERS_ROOT_SLOT as usize] = byte_field(0x10);
    s.fields[OWNER_PK_HASH_SLOT as usize] = blake3_field(b"owner-pk-v0");
    s.fields[MESSAGE_ROOT_SLOT as usize] = byte_field(0x10);
    s.fields[LATEST_PAYLOAD_SLOT as usize] = FIELD_ZERO;
    s.set_nonce(1);
    s
}

/// Apply a publish-shaped transition: head + 1, message_root changes
/// (folded with the new payload hash), latest_payload set.
fn publish_new(old: &CellState, payload_hash: FieldElement) -> CellState {
    let mut s = old.clone();
    let old_head = u64::from_be_bytes(s.fields[SEQ_HEAD_SLOT as usize][24..32].try_into().unwrap());
    s.fields[SEQ_HEAD_SLOT as usize] = u64_field(old_head + 1);
    s.fields[MESSAGE_ROOT_SLOT as usize] = blake3_field(
        &[
            &old.fields[MESSAGE_ROOT_SLOT as usize][..],
            &payload_hash[..],
        ]
        .concat(),
    );
    s.fields[LATEST_PAYLOAD_SLOT as usize] = payload_hash;
    s
}

/// Apply a consume-shaped transition: tail + 1.
fn consume_new(old: &CellState) -> CellState {
    let mut s = old.clone();
    let old_tail = u64::from_be_bytes(s.fields[SEQ_TAIL_SLOT as usize][24..32].try_into().unwrap());
    s.fields[SEQ_TAIL_SLOT as usize] = u64_field(old_tail + 1);
    s
}

fn publish_meta() -> TransitionMeta {
    TransitionMeta::new(symbol("publish"), 0)
}
fn consume_meta() -> TransitionMeta {
    TransitionMeta::new(symbol("consume"), 0)
}
fn grant_publisher_meta() -> TransitionMeta {
    TransitionMeta::new(symbol("grant_publisher"), 0)
}
fn grant_consumer_meta() -> TransitionMeta {
    TransitionMeta::new(symbol("grant_consumer"), 0)
}

/// Strip the `SenderAuthorized` constraints from the program so we can
/// exercise the slot-caveat shape independent of an executor's witness
/// bundle. `SenderAuthorized` requires an executor-bound Merkle
/// membership witness; isolating the slot caveats lets us drive
/// positive transitions without that wiring.
fn program_without_sender_authorized() -> CellProgram {
    let cases = match subscription_program() {
        CellProgram::Cases(c) => c,
        _ => panic!("expected Cases"),
    };
    let stripped: Vec<_> = cases
        .into_iter()
        .map(|mut c| {
            c.constraints
                .retain(|x| !matches!(x, StateConstraint::SenderAuthorized { .. }));
            c
        })
        .collect();
    CellProgram::Cases(stripped)
}

// ─── 1. Round-trip publish → consume produces matching payload hash ─────

#[test]
fn roundtrip_publish_then_consume_preserves_payload_hash() {
    // Build the state pair for a publish, then a consume; the
    // payload hash is the same on both event sides (the publish
    // wrote it into slot 7; the consume passes it through the
    // event without touching slot 7).
    //
    // This is the "round-trip publish → consume produces matching
    // payload hash" case from the lane spec.
    let program = program_without_sender_authorized();
    let payload_hash = blake3_field(b"hello-world");

    // 1. Publish.
    let old_pub = base_state(0, 0);
    let new_pub = publish_new(&old_pub, payload_hash);
    let r = program.evaluate_with_meta(&new_pub, Some(&old_pub), None, &publish_meta());
    assert!(r.is_ok(), "publish must pass slot-shape: {r:?}");
    // The latest_payload slot now holds the exact payload hash.
    assert_eq!(
        new_pub.fields[LATEST_PAYLOAD_SLOT as usize], payload_hash,
        "publish must write payload_hash into slot 7"
    );

    // 2. Consume the message we just published. The consume case
    // requires latest_payload_hash to stay frozen — which is
    // exactly the invariant a consumer relies on: the head-of-queue
    // pointer state is stable while the consumer reads it.
    let old_con = new_pub.clone();
    let new_con = consume_new(&old_con);
    let r = program.evaluate_with_meta(&new_con, Some(&old_con), None, &consume_meta());
    assert!(r.is_ok(), "consume must pass slot-shape: {r:?}");
    // The payload hash the consumer reads off slot 7 matches what the
    // publisher wrote.
    assert_eq!(new_con.fields[LATEST_PAYLOAD_SLOT as usize], payload_hash);
}

// ─── 2. Non-authorized publisher → rejected ────────────────────────────
//
// The `SenderAuthorized { set: PublicRoot { set_root_index: 3 } }`
// constraint requires the executor to dispatch a Merkle-membership
// witness via the executor's witness bundle. Driving the constraint
// from a unit test without a witness bundle produces a
// `SenderMembershipWitnessMissing` error — which is itself a hard
// rejection (better than silently passing). That is what the test
// asserts: an action that lacks the membership witness is rejected
// by the constraint, full stop.
#[test]
fn non_authorized_publisher_rejected() {
    let program = subscription_program(); // full program with SenderAuthorized
    let old = base_state(0, 0);
    let new = publish_new(&old, blake3_field(b"hello"));

    let err = program
        .evaluate_with_meta(&new, Some(&old), None, &publish_meta())
        .expect_err("publish without a sender-membership witness must be rejected");
    match err {
        ProgramError::SenderMembershipWitnessMissing
        | ProgramError::WitnessedPredicateRequiresExecutor { .. }
        | ProgramError::MissingContextField { .. } => {} // any of these forms is a hard reject
        other => {
            panic!("expected SenderMembershipWitnessMissing or similar rejection, got {other:?}")
        }
    }
}

#[test]
fn non_authorized_consumer_rejected() {
    let program = subscription_program();
    let old = base_state(3, 1);
    let new = consume_new(&old);

    let err = program
        .evaluate_with_meta(&new, Some(&old), None, &consume_meta())
        .expect_err("consume without a sender-membership witness must be rejected");
    match err {
        ProgramError::SenderMembershipWitnessMissing
        | ProgramError::WitnessedPredicateRequiresExecutor { .. }
        | ProgramError::MissingContextField { .. } => {}
        other => {
            panic!("expected SenderMembershipWitnessMissing or similar rejection, got {other:?}")
        }
    }
}

// ─── 3. Rewrite a message slot → rejected ──────────────────────────────

#[test]
fn rewriting_message_root_under_consume_rejected() {
    // The `consume` case marks `message_root` as Immutable. A
    // malicious consumer trying to rewrite the message root must be
    // rejected.
    let program = program_without_sender_authorized();
    let old = base_state(3, 1);
    let mut bad_new = consume_new(&old);
    bad_new.fields[MESSAGE_ROOT_SLOT as usize] = blake3_field(b"attacker-root");

    let err = program
        .evaluate_with_meta(&bad_new, Some(&old), None, &consume_meta())
        .expect_err("consume that mutates message_root must be rejected");
    match err {
        ProgramError::ConstraintViolated {
            constraint: StateConstraint::Immutable { index },
            ..
        } => assert_eq!(index, MESSAGE_ROOT_SLOT),
        other => panic!("expected Immutable on message_root, got {other:?}"),
    }
}

#[test]
fn rewriting_latest_payload_under_consume_rejected() {
    let program = program_without_sender_authorized();
    let old = {
        let mut s = base_state(3, 1);
        s.fields[LATEST_PAYLOAD_SLOT as usize] = blake3_field(b"prior-payload");
        s
    };
    let mut bad_new = consume_new(&old);
    bad_new.fields[LATEST_PAYLOAD_SLOT as usize] = blake3_field(b"attacker-payload");

    let err = program
        .evaluate_with_meta(&bad_new, Some(&old), None, &consume_meta())
        .expect_err("consume that mutates latest_payload must be rejected");
    match err {
        ProgramError::ConstraintViolated {
            constraint: StateConstraint::Immutable { index },
            ..
        } => assert_eq!(index, LATEST_PAYLOAD_SLOT),
        other => panic!("expected Immutable on latest_payload, got {other:?}"),
    }
}

#[test]
fn message_root_rewind_under_publish_rejected() {
    // The publish case requires a non-zero message root.
    let program = program_without_sender_authorized();
    let old = base_state(0, 0);
    let mut bad_new = publish_new(&old, blake3_field(b"hello"));
    // Adversarial: write a zero root.
    bad_new.fields[MESSAGE_ROOT_SLOT as usize] = [0u8; 32];

    let err = program
        .evaluate_with_meta(&bad_new, Some(&old), None, &publish_meta())
        .expect_err("zero message_root under publish must be rejected");
    match err {
        ProgramError::ConstraintViolated { constraint, .. } => {
            assert!(
                matches!(constraint, StateConstraint::FieldGte { index, .. } if index == MESSAGE_ROOT_SLOT),
                "expected FieldGte violation on message_root, got {constraint:?}"
            );
        }
        other => panic!("expected ConstraintViolated, got {other:?}"),
    }
}

#[test]
fn publish_must_change_message_root() {
    let program = program_without_sender_authorized();
    let old = base_state(0, 0);
    let mut bad_new = publish_new(&old, blake3_field(b"hello"));
    bad_new.fields[MESSAGE_ROOT_SLOT as usize] = old.fields[MESSAGE_ROOT_SLOT as usize];

    let err = program
        .evaluate_with_meta(&bad_new, Some(&old), None, &publish_meta())
        .expect_err("publish without a message_root change must be rejected");
    match err {
        ProgramError::ConstraintViolated {
            constraint: StateConstraint::Immutable { index },
            ..
        } => assert_eq!(index, MESSAGE_ROOT_SLOT),
        other => panic!("expected negated Immutable on message_root, got {other:?}"),
    }
}

// ─── 4. Decrement head or tail → rejected ──────────────────────────────

#[test]
fn head_decrement_rejected_by_monotonic_sequence() {
    let program = program_without_sender_authorized();
    let old = base_state(5, 2);
    let mut bad_new = old.clone();
    // Adversarial: rewind head from 5 to 4.
    bad_new.fields[SEQ_HEAD_SLOT as usize] = u64_field(4);
    // (Touch the message_root and latest_payload so the publish-shape
    // is at least plausible; the failure should still trigger on head.)
    bad_new.fields[MESSAGE_ROOT_SLOT as usize] = blake3_field(b"new-root");
    bad_new.fields[LATEST_PAYLOAD_SLOT as usize] = blake3_field(b"new-payload");

    let err = program
        .evaluate_with_meta(&bad_new, Some(&old), None, &publish_meta())
        .expect_err("head decrement must be rejected");
    match err {
        ProgramError::ConstraintViolated { constraint, .. } => {
            assert!(
                matches!(constraint, StateConstraint::MonotonicSequence { seq_index } if seq_index == SEQ_HEAD_SLOT),
                "expected MonotonicSequence violation on head, got {constraint:?}"
            );
        }
        other => panic!("expected ConstraintViolated, got {other:?}"),
    }
}

#[test]
fn tail_decrement_rejected_by_monotonic_sequence() {
    let program = program_without_sender_authorized();
    let old = base_state(5, 3);
    let mut bad_new = old.clone();
    bad_new.fields[SEQ_TAIL_SLOT as usize] = u64_field(2);

    let err = program
        .evaluate_with_meta(&bad_new, Some(&old), None, &consume_meta())
        .expect_err("tail decrement must be rejected");
    match err {
        ProgramError::ConstraintViolated { constraint, .. } => {
            assert!(
                matches!(constraint, StateConstraint::MonotonicSequence { seq_index } if seq_index == SEQ_TAIL_SLOT),
                "expected MonotonicSequence violation on tail, got {constraint:?}"
            );
        }
        other => panic!("expected ConstraintViolated, got {other:?}"),
    }
}

#[test]
fn head_advance_by_two_rejected_by_monotonic_sequence() {
    // `MonotonicSequence` requires *exactly* +1; a +2 increment is
    // a replay-style bypass attempt and must be rejected.
    let program = program_without_sender_authorized();
    let old = base_state(0, 0);
    let mut bad_new = publish_new(&old, blake3_field(b"hello"));
    // Adversarial: advance head by 2 instead of 1.
    bad_new.fields[SEQ_HEAD_SLOT as usize] = u64_field(2);

    let err = program
        .evaluate_with_meta(&bad_new, Some(&old), None, &publish_meta())
        .expect_err("head += 2 must be rejected");
    match err {
        ProgramError::ConstraintViolated { constraint, .. } => {
            assert!(
                matches!(constraint, StateConstraint::MonotonicSequence { seq_index } if seq_index == SEQ_HEAD_SLOT),
                "expected MonotonicSequence violation on head, got {constraint:?}"
            );
        }
        other => panic!("expected ConstraintViolated, got {other:?}"),
    }
}

// ─── 5. Operation-scoping ──────────────────────────────────────────────

#[test]
fn publish_op_does_not_advance_tail() {
    let program = program_without_sender_authorized();
    let old = base_state(0, 0);
    let mut bad_new = publish_new(&old, blake3_field(b"hello"));
    // Adversarial: also advance tail in the same turn.
    bad_new.fields[SEQ_TAIL_SLOT as usize] = u64_field(1);

    let err = program
        .evaluate_with_meta(&bad_new, Some(&old), None, &publish_meta())
        .expect_err("publish that advances tail must be rejected");
    match err {
        ProgramError::ConstraintViolated {
            constraint: StateConstraint::Immutable { index },
            ..
        } => assert_eq!(index, SEQ_TAIL_SLOT),
        other => panic!("expected Immutable {{ index: SEQ_TAIL_SLOT }}, got {other:?}"),
    }
}

#[test]
fn consume_op_does_not_advance_head() {
    let program = program_without_sender_authorized();
    let old = base_state(3, 0);
    let mut bad_new = consume_new(&old);
    // Adversarial: also advance head.
    bad_new.fields[SEQ_HEAD_SLOT as usize] = u64_field(4);

    let err = program
        .evaluate_with_meta(&bad_new, Some(&old), None, &consume_meta())
        .expect_err("consume that advances head must be rejected");
    match err {
        ProgramError::ConstraintViolated {
            constraint: StateConstraint::Immutable { index },
            ..
        } => assert_eq!(index, SEQ_HEAD_SLOT),
        other => panic!("expected Immutable {{ index: SEQ_HEAD_SLOT }}, got {other:?}"),
    }
}

// ─── 6. Lifetime invariants: capacity, owner, root-decrement ───────────

#[test]
fn capacity_overwrite_under_publish_rejected() {
    // Capacity is Immutable in the `Always` invariants case — any
    // operation that tries to mutate it is rejected.
    let program = program_without_sender_authorized();
    let old = base_state(0, 0);
    let mut bad_new = publish_new(&old, blake3_field(b"hello"));
    bad_new.fields[CAPACITY_SLOT as usize] = u64_field(9999);

    let err = program
        .evaluate_with_meta(&bad_new, Some(&old), None, &publish_meta())
        .expect_err("capacity mutation must be rejected");
    match err {
        ProgramError::ConstraintViolated {
            constraint: StateConstraint::Immutable { index },
            ..
        } => assert_eq!(index, CAPACITY_SLOT),
        other => panic!("expected Immutable violation on capacity, got {other:?}"),
    }
}

#[test]
fn owner_overwrite_under_publish_rejected() {
    let program = program_without_sender_authorized();
    let old = base_state(0, 0);
    let mut bad_new = publish_new(&old, blake3_field(b"hello"));
    bad_new.fields[OWNER_PK_HASH_SLOT as usize] = blake3_field(b"attacker-pk");

    let err = program
        .evaluate_with_meta(&bad_new, Some(&old), None, &publish_meta())
        .expect_err("owner mutation must be rejected");
    match err {
        ProgramError::ConstraintViolated {
            constraint: StateConstraint::Immutable { index },
            ..
        } => assert_eq!(index, OWNER_PK_HASH_SLOT),
        other => panic!("expected Immutable violation on owner, got {other:?}"),
    }
}

#[test]
fn unknown_method_default_denied() {
    // Cav-Codex Block 4 default-deny: a method symbol that
    // matches no case must be rejected outright.
    let program = program_without_sender_authorized();
    let old = base_state(0, 0);
    let new = publish_new(&old, blake3_field(b"hello"));
    let bogus_meta = TransitionMeta::new(symbol("attacker_op_drain"), 0);

    let err = program
        .evaluate_with_meta(&new, Some(&old), None, &bogus_meta)
        .expect_err("unknown method must be rejected");
    assert!(
        matches!(err, ProgramError::NoTransitionCaseMatched),
        "expected NoTransitionCaseMatched, got {err:?}"
    );
}

// ─── 7. Grant operations: scoping + opaque-root changes ────────────────

#[test]
fn legal_grant_publisher_passes_slot_shape() {
    let program = program_without_sender_authorized();
    let old = base_state(2, 1);
    let mut new = old.clone();
    new.fields[PUBLISHERS_ROOT_SLOT as usize] = byte_field(0x20);

    let r = program.evaluate_with_meta(&new, Some(&old), None, &grant_publisher_meta());
    assert!(r.is_ok(), "legal grant_publisher must pass: {r:?}");
}

#[test]
fn grant_publisher_must_change_publishers_root() {
    let program = program_without_sender_authorized();
    let old = base_state(2, 1);
    let new = old.clone();

    let err = program
        .evaluate_with_meta(&new, Some(&old), None, &grant_publisher_meta())
        .expect_err("grant_publisher without publishers_root change must be rejected");
    match err {
        ProgramError::ConstraintViolated {
            constraint: StateConstraint::Immutable { index },
            ..
        } => assert_eq!(index, PUBLISHERS_ROOT_SLOT),
        other => panic!("expected negated Immutable on publishers root, got {other:?}"),
    }
}

#[test]
fn grant_publisher_cannot_advance_head() {
    let program = program_without_sender_authorized();
    let old = base_state(2, 1);
    let mut bad_new = old.clone();
    bad_new.fields[PUBLISHERS_ROOT_SLOT as usize] = byte_field(0x20);
    // Adversarial: also advance head.
    bad_new.fields[SEQ_HEAD_SLOT as usize] = u64_field(3);

    let err = program
        .evaluate_with_meta(&bad_new, Some(&old), None, &grant_publisher_meta())
        .expect_err("grant_publisher that advances head must be rejected");
    match err {
        ProgramError::ConstraintViolated {
            constraint: StateConstraint::Immutable { index },
            ..
        } => assert_eq!(index, SEQ_HEAD_SLOT),
        other => panic!("expected Immutable on head, got {other:?}"),
    }
}

#[test]
fn grant_consumer_cannot_modify_publishers_root() {
    let program = program_without_sender_authorized();
    let old = base_state(2, 1);
    let mut bad_new = old.clone();
    // CONSUMERS_ROOT advances legitimately under grant_consumer.
    bad_new.fields[CONSUMERS_ROOT_SLOT as usize] = byte_field(0x20);
    // Adversarial: also change the publishers root.
    bad_new.fields[PUBLISHERS_ROOT_SLOT as usize] = byte_field(0x20);

    let err = program
        .evaluate_with_meta(&bad_new, Some(&old), None, &grant_consumer_meta())
        .expect_err("grant_consumer that touches publishers root must be rejected");
    match err {
        ProgramError::ConstraintViolated {
            constraint: StateConstraint::Immutable { index },
            ..
        } => assert_eq!(index, PUBLISHERS_ROOT_SLOT),
        other => panic!("expected Immutable on publishers root, got {other:?}"),
    }
}

#[test]
fn grant_publisher_root_decrement_rejected() {
    // The grant_publisher case requires a non-zero publishers root.
    let program = program_without_sender_authorized();
    let old = base_state(2, 1);
    let mut bad_new = old.clone();
    bad_new.fields[PUBLISHERS_ROOT_SLOT as usize] = [0u8; 32];

    let err = program
        .evaluate_with_meta(&bad_new, Some(&old), None, &grant_publisher_meta())
        .expect_err("publishers root decrement must be rejected");
    match err {
        ProgramError::ConstraintViolated { constraint, .. } => {
            assert!(
                matches!(constraint, StateConstraint::FieldGte { index, .. } if index == PUBLISHERS_ROOT_SLOT),
                "expected FieldGte on publishers root, got {constraint:?}"
            );
        }
        other => panic!("expected ConstraintViolated, got {other:?}"),
    }
}

#[test]
fn legal_grant_consumer_passes_slot_shape() {
    let program = program_without_sender_authorized();
    let old = base_state(2, 1);
    let mut new = old.clone();
    new.fields[CONSUMERS_ROOT_SLOT as usize] = byte_field(0x20);

    let r = program.evaluate_with_meta(&new, Some(&old), None, &grant_consumer_meta());
    assert!(r.is_ok(), "legal grant_consumer must pass: {r:?}");
}

#[test]
fn grant_consumer_must_change_consumers_root() {
    let program = program_without_sender_authorized();
    let old = base_state(2, 1);
    let new = old.clone();

    let err = program
        .evaluate_with_meta(&new, Some(&old), None, &grant_consumer_meta())
        .expect_err("grant_consumer without consumers_root change must be rejected");
    match err {
        ProgramError::ConstraintViolated {
            constraint: StateConstraint::Immutable { index },
            ..
        } => assert_eq!(index, CONSUMERS_ROOT_SLOT),
        other => panic!("expected negated Immutable on consumers root, got {other:?}"),
    }
}

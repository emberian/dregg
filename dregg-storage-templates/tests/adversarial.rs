//! Adversarial transition tests for `dregg-storage-templates`.
//!
//! These exercise each template's operation-scoped semantics by
//! driving [`CellProgram::evaluate_with_meta`] against hand-rolled
//! `(old_state, new_state, TransitionMeta)` triples. They mirror the
//! pattern set by `starbridge-apps/subscription/tests/program.rs`
//! (the §3.1 proof-of-pattern). Adversarial cases are organized
//! around the §3 reference designs:
//!
//! 1. Decrement attempts on monotonic slots → rejected.
//! 2. Cross-operation pollution (e.g. enqueue advancing tail) →
//!    rejected by `Immutable`.
//! 3. Immutable invariants (capacity / owner / program_vk / etc.) →
//!    rejected.
//! 4. Default-deny on unknown methods → rejected.
//! 5. Witness-bound predicates (Custom for BlindedQueue, DFA for
//!    RelayOperator) → rejected absent witness wiring (the
//!    *executor*-side check, not the slot-caveat check, surfaces a
//!    hard reject).

use dregg_app_framework::symbol;
use dregg_cell::StateConstraint;
use dregg_cell::program::{CellProgram, ProgramError, TransitionMeta};
use dregg_cell::state::{CellState, FieldElement};

use dregg_storage_templates::{
    blinded_queue, cap_inbox, programmable_queue, pubsub_topic, relay_operator,
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

/// Strip `SenderAuthorized` + `Witnessed` constraints from a
/// program so we can exercise the slot-caveat shape independent of
/// executor witness wiring.
fn strip_witness_constraints(p: CellProgram) -> CellProgram {
    let cases = match p {
        CellProgram::Cases(c) => c,
        other => return other,
    };
    let stripped: Vec<_> = cases
        .into_iter()
        .map(|mut c| {
            c.constraints.retain(|x| {
                !matches!(
                    x,
                    StateConstraint::SenderAuthorized { .. }
                        | StateConstraint::Witnessed { .. }
                        | StateConstraint::RateLimit { .. }
                        | StateConstraint::RateLimitBySum { .. }
                )
            });
            c
        })
        .collect();
    CellProgram::Cases(stripped)
}

fn method_meta(method: &str) -> TransitionMeta {
    TransitionMeta::new(symbol(method), 0)
}

// =============================================================================
// CapInbox — §3.1 generalization
// =============================================================================

mod cap_inbox_tests {
    use super::*;
    use cap_inbox::*;

    fn base_state() -> CellState {
        let mut s = CellState::new(0);
        s.fields[CAPACITY_SLOT as usize] = u64_field(8);
        s.fields[MIN_DEPOSIT_SLOT as usize] = u64_field(100);
        s.fields[OWNER_PK_HASH_SLOT as usize] = blake3_field(b"owner");
        s.fields[SENDER_SET_ROOT_SLOT as usize] = blake3_field(b"senders-v0");
        s.set_nonce(1);
        s
    }

    fn send_new(old: &CellState, payload_commitment: FieldElement, deposit: u64) -> CellState {
        let mut s = old.clone();
        let head = u64::from_be_bytes(s.fields[HEAD_SEQ_SLOT as usize][24..32].try_into().unwrap());
        let total = u64::from_be_bytes(
            s.fields[TOTAL_DEPOSITS_SLOT as usize][24..32]
                .try_into()
                .unwrap(),
        );
        s.fields[HEAD_SEQ_SLOT as usize] = u64_field(head + 1);
        s.fields[TOTAL_DEPOSITS_SLOT as usize] = u64_field(total + deposit);
        s.fields[MESSAGE_ROOT_SLOT as usize] = blake3_field(
            &[
                &old.fields[MESSAGE_ROOT_SLOT as usize][..],
                &payload_commitment[..],
            ]
            .concat(),
        );
        s
    }

    fn dequeue_new(old: &CellState) -> CellState {
        let mut s = old.clone();
        let tail = u64::from_be_bytes(s.fields[TAIL_SEQ_SLOT as usize][24..32].try_into().unwrap());
        s.fields[TAIL_SEQ_SLOT as usize] = u64_field(tail + 1);
        s
    }

    #[test]
    fn legal_send_passes() {
        let p = strip_witness_constraints(cap_inbox_program());
        let old = base_state();
        let new = send_new(&old, blake3_field(b"msg"), 100);
        let r = p.evaluate_with_meta(&new, Some(&old), None, &method_meta("send"));
        assert!(r.is_ok(), "legal send must pass: {r:?}");
    }

    #[test]
    fn legal_dequeue_passes() {
        let p = strip_witness_constraints(cap_inbox_program());
        let mut old = base_state();
        old.fields[HEAD_SEQ_SLOT as usize] = u64_field(3);
        old.fields[TAIL_SEQ_SLOT as usize] = u64_field(0);
        old.fields[MESSAGE_ROOT_SLOT as usize] = blake3_field(b"some-ring");
        let new = dequeue_new(&old);
        let r = p.evaluate_with_meta(&new, Some(&old), None, &method_meta("dequeue"));
        assert!(r.is_ok(), "legal dequeue must pass: {r:?}");
    }

    #[test]
    fn capacity_overwrite_rejected() {
        let p = strip_witness_constraints(cap_inbox_program());
        let old = base_state();
        let mut bad = send_new(&old, blake3_field(b"msg"), 100);
        bad.fields[CAPACITY_SLOT as usize] = u64_field(9999);
        let err = p
            .evaluate_with_meta(&bad, Some(&old), None, &method_meta("send"))
            .expect_err("capacity mutation must be rejected");
        match err {
            ProgramError::ConstraintViolated {
                constraint: StateConstraint::Immutable { index },
                ..
            } => assert_eq!(index, CAPACITY_SLOT),
            other => panic!("expected Immutable on capacity, got {other:?}"),
        }
    }

    #[test]
    fn min_deposit_overwrite_rejected() {
        let p = strip_witness_constraints(cap_inbox_program());
        let old = base_state();
        let mut bad = send_new(&old, blake3_field(b"msg"), 100);
        bad.fields[MIN_DEPOSIT_SLOT as usize] = u64_field(1);
        let err = p
            .evaluate_with_meta(&bad, Some(&old), None, &method_meta("send"))
            .expect_err("min_deposit mutation must be rejected");
        match err {
            ProgramError::ConstraintViolated {
                constraint: StateConstraint::Immutable { index },
                ..
            } => assert_eq!(index, MIN_DEPOSIT_SLOT),
            other => panic!("expected Immutable on min_deposit, got {other:?}"),
        }
    }

    #[test]
    fn send_cannot_advance_tail() {
        let p = strip_witness_constraints(cap_inbox_program());
        let old = base_state();
        let mut bad = send_new(&old, blake3_field(b"msg"), 100);
        bad.fields[TAIL_SEQ_SLOT as usize] = u64_field(1);
        let err = p
            .evaluate_with_meta(&bad, Some(&old), None, &method_meta("send"))
            .expect_err("send that advances tail must be rejected");
        match err {
            ProgramError::ConstraintViolated {
                constraint: StateConstraint::Immutable { index },
                ..
            } => assert_eq!(index, TAIL_SEQ_SLOT),
            other => panic!("expected Immutable on tail, got {other:?}"),
        }
    }

    #[test]
    fn head_decrement_rejected() {
        let p = strip_witness_constraints(cap_inbox_program());
        let mut old = base_state();
        old.fields[HEAD_SEQ_SLOT as usize] = u64_field(5);
        let mut bad = old.clone();
        bad.fields[HEAD_SEQ_SLOT as usize] = u64_field(4);
        bad.fields[MESSAGE_ROOT_SLOT as usize] = blake3_field(b"x");
        bad.fields[TOTAL_DEPOSITS_SLOT as usize] = u64_field(100);
        let err = p
            .evaluate_with_meta(&bad, Some(&old), None, &method_meta("send"))
            .expect_err("head decrement must be rejected");
        assert!(matches!(err, ProgramError::ConstraintViolated { .. }));
    }

    #[test]
    fn unknown_method_default_denied() {
        let p = strip_witness_constraints(cap_inbox_program());
        let old = base_state();
        let new = send_new(&old, blake3_field(b"x"), 100);
        let err = p
            .evaluate_with_meta(&new, Some(&old), None, &method_meta("attacker_drain"))
            .expect_err("unknown method must be rejected");
        assert!(matches!(err, ProgramError::NoTransitionCaseMatched));
    }
}

// =============================================================================
// ProgrammableQueue — §3.2 canonical mapping
// =============================================================================

mod programmable_queue_tests {
    use super::*;
    use programmable_queue::*;

    fn base_state() -> CellState {
        let mut s = CellState::new(0);
        s.fields[CAPACITY_SLOT as usize] = u64_field(8);
        s.fields[PROGRAM_VK_SLOT as usize] = blake3_field(b"program-vk-v0");
        s.fields[OWNER_PK_HASH_SLOT as usize] = blake3_field(b"owner");
        s.fields[SENDER_SET_ROOT_SLOT as usize] = blake3_field(b"senders-v0");
        s.fields[CONTENT_PATTERN_ROOT_SLOT as usize] = blake3_field(b"pattern-v0");
        s.set_nonce(1);
        s
    }

    fn enqueue_new(old: &CellState) -> CellState {
        let mut s = old.clone();
        let head = u64::from_be_bytes(s.fields[HEAD_SEQ_SLOT as usize][24..32].try_into().unwrap());
        s.fields[HEAD_SEQ_SLOT as usize] = u64_field(head + 1);
        s.fields[RING_ROOT_SLOT as usize] = blake3_field(b"new-ring");
        s
    }

    #[test]
    fn legal_enqueue_passes() {
        let p = strip_witness_constraints(programmable_queue_program());
        let old = base_state();
        let new = enqueue_new(&old);
        let r = p.evaluate_with_meta(&new, Some(&old), None, &method_meta("enqueue"));
        assert!(r.is_ok(), "legal enqueue must pass: {r:?}");
    }

    #[test]
    fn program_vk_overwrite_rejected() {
        let p = strip_witness_constraints(programmable_queue_program());
        let old = base_state();
        let mut bad = enqueue_new(&old);
        bad.fields[PROGRAM_VK_SLOT as usize] = blake3_field(b"attacker-vk");
        let err = p
            .evaluate_with_meta(&bad, Some(&old), None, &method_meta("enqueue"))
            .expect_err("program_vk mutation must be rejected");
        match err {
            ProgramError::ConstraintViolated {
                constraint: StateConstraint::Immutable { index },
                ..
            } => assert_eq!(index, PROGRAM_VK_SLOT),
            other => panic!("expected Immutable on program_vk, got {other:?}"),
        }
    }

    #[test]
    fn enqueue_cannot_change_sender_set_root() {
        let p = strip_witness_constraints(programmable_queue_program());
        let old = base_state();
        let mut bad = enqueue_new(&old);
        bad.fields[SENDER_SET_ROOT_SLOT as usize] = blake3_field(b"attacker-set");
        let err = p
            .evaluate_with_meta(&bad, Some(&old), None, &method_meta("enqueue"))
            .expect_err("sender_set_root must be Immutable during enqueue");
        match err {
            ProgramError::ConstraintViolated {
                constraint: StateConstraint::Immutable { index },
                ..
            } => assert_eq!(index, SENDER_SET_ROOT_SLOT),
            other => panic!("expected Immutable on sender_set_root, got {other:?}"),
        }
    }

    #[test]
    fn enqueue_must_change_ring_root() {
        let p = strip_witness_constraints(programmable_queue_program());
        let old = base_state();
        let mut bad = old.clone();
        bad.fields[HEAD_SEQ_SLOT as usize] = u64_field(1);

        let err = p
            .evaluate_with_meta(&bad, Some(&old), None, &method_meta("enqueue"))
            .expect_err("enqueue without ring_root change must be rejected");
        match err {
            ProgramError::ConstraintViolated {
                constraint: StateConstraint::Immutable { index },
                ..
            } => assert_eq!(index, RING_ROOT_SLOT),
            other => panic!("expected negated Immutable on ring_root, got {other:?}"),
        }
    }

    #[test]
    fn grant_sender_must_change_sender_root() {
        let p = strip_witness_constraints(programmable_queue_program());
        let old = base_state();
        let new = old.clone();

        let err = p
            .evaluate_with_meta(&new, Some(&old), None, &method_meta("grant_sender"))
            .expect_err("grant_sender without sender_set_root change must be rejected");
        match err {
            ProgramError::ConstraintViolated {
                constraint: StateConstraint::Immutable { index },
                ..
            } => assert_eq!(index, SENDER_SET_ROOT_SLOT),
            other => panic!("expected negated Immutable on sender_set_root, got {other:?}"),
        }
    }
}

// =============================================================================
// PubSubTopic — §3.3
// =============================================================================

mod pubsub_topic_tests {
    use super::*;
    use pubsub_topic::*;

    fn base_state() -> CellState {
        let mut s = CellState::new(0);
        s.fields[PUBLISHER_PK_HASH_SLOT as usize] = blake3_field(b"publisher");
        s.fields[TOPIC_ID_HASH_SLOT as usize] = blake3_field(b"topic-id");
        s.fields[TOPIC_FILTER_ROOT_SLOT as usize] = blake3_field(b"filter-v0");
        s.set_nonce(1);
        s
    }

    fn publish_new(old: &CellState) -> CellState {
        let mut s = old.clone();
        let head = u64::from_be_bytes(s.fields[HEAD_SEQ_SLOT as usize][24..32].try_into().unwrap());
        s.fields[HEAD_SEQ_SLOT as usize] = u64_field(head + 1);
        s.fields[EVENT_ROOT_SLOT as usize] = blake3_field(b"events-v1");
        s.fields[DEDUP_ROOT_SLOT as usize] = blake3_field(b"dedup-v1");
        s
    }

    #[test]
    fn legal_publish_passes() {
        let p = strip_witness_constraints(pubsub_topic_program());
        let old = base_state();
        let new = publish_new(&old);
        let r = p.evaluate_with_meta(&new, Some(&old), None, &method_meta("publish"));
        assert!(r.is_ok(), "legal publish must pass: {r:?}");
    }

    #[test]
    fn topic_id_overwrite_rejected() {
        let p = strip_witness_constraints(pubsub_topic_program());
        let old = base_state();
        let mut bad = publish_new(&old);
        bad.fields[TOPIC_ID_HASH_SLOT as usize] = blake3_field(b"attacker-id");
        let err = p
            .evaluate_with_meta(&bad, Some(&old), None, &method_meta("publish"))
            .expect_err("topic_id mutation must be rejected");
        match err {
            ProgramError::ConstraintViolated {
                constraint: StateConstraint::Immutable { index },
                ..
            } => assert_eq!(index, TOPIC_ID_HASH_SLOT),
            other => panic!("expected Immutable on topic_id, got {other:?}"),
        }
    }

    #[test]
    fn topic_filter_root_overwrite_rejected() {
        // The filter root is immutable for the lifetime of the
        // topic: a malicious publisher cannot change the DFA after
        // creation.
        let p = strip_witness_constraints(pubsub_topic_program());
        let old = base_state();
        let mut bad = publish_new(&old);
        bad.fields[TOPIC_FILTER_ROOT_SLOT as usize] = blake3_field(b"attacker-filter");
        let err = p
            .evaluate_with_meta(&bad, Some(&old), None, &method_meta("publish"))
            .expect_err("filter root must be Immutable");
        match err {
            ProgramError::ConstraintViolated {
                constraint: StateConstraint::Immutable { index },
                ..
            } => assert_eq!(index, TOPIC_FILTER_ROOT_SLOT),
            other => panic!("expected Immutable on topic_filter_root, got {other:?}"),
        }
    }

    #[test]
    fn event_root_rewind_rejected() {
        let p = strip_witness_constraints(pubsub_topic_program());
        let mut old = base_state();
        old.fields[HEAD_SEQ_SLOT as usize] = u64_field(5);
        old.fields[EVENT_ROOT_SLOT as usize] = blake3_field(b"events-v5");
        let mut bad = publish_new(&old);
        // Rewind event root (set it to zero).
        bad.fields[EVENT_ROOT_SLOT as usize] = [0u8; 32];
        let err = p
            .evaluate_with_meta(&bad, Some(&old), None, &method_meta("publish"))
            .expect_err("event root rewind must be rejected");
        assert!(matches!(err, ProgramError::ConstraintViolated { .. }));
    }

    #[test]
    fn publish_must_change_event_and_dedup_roots() {
        let p = strip_witness_constraints(pubsub_topic_program());
        let old = base_state();

        let mut bad_event = publish_new(&old);
        bad_event.fields[EVENT_ROOT_SLOT as usize] = old.fields[EVENT_ROOT_SLOT as usize];
        let err = p
            .evaluate_with_meta(&bad_event, Some(&old), None, &method_meta("publish"))
            .expect_err("publish without event_root change must be rejected");
        match err {
            ProgramError::ConstraintViolated {
                constraint: StateConstraint::Immutable { index },
                ..
            } => assert_eq!(index, EVENT_ROOT_SLOT),
            other => panic!("expected negated Immutable on event_root, got {other:?}"),
        }

        let mut bad_dedup = publish_new(&old);
        bad_dedup.fields[DEDUP_ROOT_SLOT as usize] = old.fields[DEDUP_ROOT_SLOT as usize];
        let err = p
            .evaluate_with_meta(&bad_dedup, Some(&old), None, &method_meta("publish"))
            .expect_err("publish without dedup_root change must be rejected");
        match err {
            ProgramError::ConstraintViolated {
                constraint: StateConstraint::Immutable { index },
                ..
            } => assert_eq!(index, DEDUP_ROOT_SLOT),
            other => panic!("expected negated Immutable on dedup_root, got {other:?}"),
        }
    }

    #[test]
    fn subscribe_must_change_cursor_root() {
        let p = strip_witness_constraints(pubsub_topic_program());
        let old = base_state();
        let new = old.clone();

        let err = p
            .evaluate_with_meta(&new, Some(&old), None, &method_meta("subscribe"))
            .expect_err("subscribe without subscriber_cursors_root change must be rejected");
        match err {
            ProgramError::ConstraintViolated {
                constraint: StateConstraint::Immutable { index },
                ..
            } => assert_eq!(index, SUBSCRIBER_CURSORS_ROOT_SLOT),
            other => panic!("expected negated Immutable on subscriber_cursors_root, got {other:?}"),
        }
    }

    #[test]
    fn grant_subscriber_must_change_subscriber_set_root() {
        let p = strip_witness_constraints(pubsub_topic_program());
        let old = base_state();
        let new = old.clone();

        let err = p
            .evaluate_with_meta(&new, Some(&old), None, &method_meta("grant_subscriber"))
            .expect_err("grant_subscriber without subscriber_set_root change must be rejected");
        match err {
            ProgramError::ConstraintViolated {
                constraint: StateConstraint::Immutable { index },
                ..
            } => assert_eq!(index, SUBSCRIBER_SET_ROOT_SLOT),
            other => panic!("expected negated Immutable on subscriber_set_root, got {other:?}"),
        }
    }
}

// =============================================================================
// BlindedQueue — §3.4
// =============================================================================

mod blinded_queue_tests {
    use super::*;
    use blinded_queue::*;

    fn base_state() -> CellState {
        let mut s = CellState::new(0);
        s.fields[CAPACITY_SLOT as usize] = u64_field(8);
        s.fields[CONSUMER_PK_HASH_SLOT as usize] = blake3_field(b"consumer");
        s.fields[SPEND_AIR_VK_COMMITMENT_SLOT as usize] = BLINDED_QUEUE_SPEND_AIR_VK;
        s.fields[QUEUE_ID_HASH_SLOT as usize] = blake3_field(b"queue-id");
        s.set_nonce(1);
        s
    }

    fn add_new(old: &CellState) -> CellState {
        let mut s = old.clone();
        let count = u64::from_be_bytes(
            s.fields[COMMITMENT_COUNT_SLOT as usize][24..32]
                .try_into()
                .unwrap(),
        );
        s.fields[COMMITMENT_COUNT_SLOT as usize] = u64_field(count + 1);
        s.fields[COMMITMENTS_ROOT_SLOT as usize] = blake3_field(b"commitments-v1");
        s
    }

    #[test]
    fn legal_add_passes() {
        let p = strip_witness_constraints(blinded_queue_program());
        let old = base_state();
        let new = add_new(&old);
        let r = p.evaluate_with_meta(&new, Some(&old), None, &method_meta("add"));
        assert!(r.is_ok(), "legal add must pass: {r:?}");
    }

    #[test]
    fn add_cannot_modify_nullifier_root() {
        let p = strip_witness_constraints(blinded_queue_program());
        let old = base_state();
        let mut bad = add_new(&old);
        bad.fields[NULLIFIER_ROOT_SLOT as usize] = blake3_field(b"attacker-nulls");
        let err = p
            .evaluate_with_meta(&bad, Some(&old), None, &method_meta("add"))
            .expect_err("add that modifies nullifier_root must be rejected");
        match err {
            ProgramError::ConstraintViolated {
                constraint: StateConstraint::Immutable { index },
                ..
            } => assert_eq!(index, NULLIFIER_ROOT_SLOT),
            other => panic!("expected Immutable on nullifier_root, got {other:?}"),
        }
    }

    #[test]
    fn consumer_pk_overwrite_rejected() {
        let p = strip_witness_constraints(blinded_queue_program());
        let old = base_state();
        let mut bad = add_new(&old);
        bad.fields[CONSUMER_PK_HASH_SLOT as usize] = blake3_field(b"attacker-consumer");
        let err = p
            .evaluate_with_meta(&bad, Some(&old), None, &method_meta("add"))
            .expect_err("consumer_pk mutation must be rejected");
        match err {
            ProgramError::ConstraintViolated {
                constraint: StateConstraint::Immutable { index },
                ..
            } => assert_eq!(index, CONSUMER_PK_HASH_SLOT),
            other => panic!("expected Immutable on consumer_pk, got {other:?}"),
        }
    }

    #[test]
    fn spend_air_vk_overwrite_rejected() {
        // Per §3.4: the spend AIR VK is bound at creation. A
        // malicious consumer cannot swap to a weaker verifier.
        let p = strip_witness_constraints(blinded_queue_program());
        let old = base_state();
        let mut bad = add_new(&old);
        bad.fields[SPEND_AIR_VK_COMMITMENT_SLOT as usize] = blake3_field(b"attacker-air");
        let err = p
            .evaluate_with_meta(&bad, Some(&old), None, &method_meta("add"))
            .expect_err("spend_air_vk swap must be rejected");
        match err {
            ProgramError::ConstraintViolated {
                constraint: StateConstraint::Immutable { index },
                ..
            } => assert_eq!(index, SPEND_AIR_VK_COMMITMENT_SLOT),
            other => panic!("expected Immutable on spend_air_vk, got {other:?}"),
        }
    }

    #[test]
    fn consume_without_witness_rejected_by_executor_hook() {
        // The consume case carries a Witnessed { Custom { vk_hash } }
        // constraint. Driven without an executor + witness registry
        // it surfaces a WitnessedPredicateRequiresExecutor error
        // (the hard-reject path).
        let p = blinded_queue_program(); // unstripped
        let mut old = base_state();
        old.fields[COMMITMENT_COUNT_SLOT as usize] = u64_field(1);
        old.fields[COMMITMENTS_ROOT_SLOT as usize] = blake3_field(b"have-an-item");
        let mut new = old.clone();
        let nc = u64::from_be_bytes(
            new.fields[NULLIFIER_COUNT_SLOT as usize][24..32]
                .try_into()
                .unwrap(),
        );
        new.fields[NULLIFIER_COUNT_SLOT as usize] = u64_field(nc + 1);
        new.fields[NULLIFIER_ROOT_SLOT as usize] = blake3_field(b"nulls-v1");

        let err = p
            .evaluate_with_meta(&new, Some(&old), None, &method_meta("consume"))
            .expect_err("consume without witness must hard-reject");
        match err {
            ProgramError::WitnessedPredicateRequiresExecutor { .. }
            | ProgramError::WitnessedPredicateRejected { .. } => {}
            other => panic!("expected witnessed-predicate hard-reject, got {other:?}"),
        }
    }
}

// =============================================================================
// RelayOperator — §3.5
// =============================================================================

mod relay_operator_tests {
    use super::*;
    use relay_operator::*;

    fn base_state() -> CellState {
        let mut s = CellState::new(0);
        s.fields[BOND_AMOUNT_SLOT as usize] = u64_field(10_000);
        s.fields[BOND_MIN_SLOT as usize] = u64_field(1_000);
        s.fields[QUOTA_BYTES_PER_EPOCH_SLOT as usize] = u64_field(1_000_000);
        s.fields[OPERATOR_PK_HASH_SLOT as usize] = blake3_field(b"operator");
        s.fields[ROUTE_TABLE_ROOT_SLOT as usize] = blake3_field(b"route-table");
        s.set_nonce(1);
        s
    }

    fn register_new(old: &CellState) -> CellState {
        let mut s = old.clone();
        s.fields[HOSTED_INBOX_ROOT_SLOT as usize] = blake3_field(b"hosted-v1");
        s
    }

    #[test]
    fn legal_register_inbox_passes_slot_shape() {
        let p = strip_witness_constraints(relay_operator_program());
        let old = base_state();
        let new = register_new(&old);
        let r = p.evaluate_with_meta(&new, Some(&old), None, &method_meta("register_inbox"));
        assert!(r.is_ok(), "legal register_inbox must pass: {r:?}");
    }

    #[test]
    fn quota_immutable_during_register() {
        let p = strip_witness_constraints(relay_operator_program());
        let old = base_state();
        let mut bad = register_new(&old);
        bad.fields[QUOTA_BYTES_PER_EPOCH_SLOT as usize] = u64_field(999_999_999);
        let err = p
            .evaluate_with_meta(&bad, Some(&old), None, &method_meta("register_inbox"))
            .expect_err("quota mutation must be rejected");
        match err {
            ProgramError::ConstraintViolated {
                constraint: StateConstraint::Immutable { index },
                ..
            } => assert_eq!(index, QUOTA_BYTES_PER_EPOCH_SLOT),
            other => panic!("expected Immutable on quota, got {other:?}"),
        }
    }

    #[test]
    fn operator_pk_immutable() {
        let p = strip_witness_constraints(relay_operator_program());
        let old = base_state();
        let mut bad = register_new(&old);
        bad.fields[OPERATOR_PK_HASH_SLOT as usize] = blake3_field(b"attacker-operator");
        let err = p
            .evaluate_with_meta(&bad, Some(&old), None, &method_meta("register_inbox"))
            .expect_err("operator pk mutation must be rejected");
        match err {
            ProgramError::ConstraintViolated {
                constraint: StateConstraint::Immutable { index },
                ..
            } => assert_eq!(index, OPERATOR_PK_HASH_SLOT),
            other => panic!("expected Immutable on operator_pk, got {other:?}"),
        }
    }

    #[test]
    fn route_table_immutable() {
        // Per §3.5: a relay operator declaring it routes pattern P
        // cannot then quietly start routing pattern Q. Route-table
        // changes require constitutional update.
        let p = strip_witness_constraints(relay_operator_program());
        let old = base_state();
        let mut bad = register_new(&old);
        bad.fields[ROUTE_TABLE_ROOT_SLOT as usize] = blake3_field(b"attacker-routes");
        let err = p
            .evaluate_with_meta(&bad, Some(&old), None, &method_meta("register_inbox"))
            .expect_err("route_table mutation must be rejected");
        match err {
            ProgramError::ConstraintViolated {
                constraint: StateConstraint::Immutable { index },
                ..
            } => assert_eq!(index, ROUTE_TABLE_ROOT_SLOT),
            other => panic!("expected Immutable on route_table_root, got {other:?}"),
        }
    }

    #[test]
    fn register_inbox_must_change_hosted_inbox_root() {
        let p = strip_witness_constraints(relay_operator_program());
        let old = base_state();
        let new = old.clone();

        let err = p
            .evaluate_with_meta(&new, Some(&old), None, &method_meta("register_inbox"))
            .expect_err("register_inbox without hosted_inbox_root change must be rejected");
        match err {
            ProgramError::ConstraintViolated {
                constraint: StateConstraint::Immutable { index },
                ..
            } => assert_eq!(index, HOSTED_INBOX_ROOT_SLOT),
            other => panic!("expected negated Immutable on hosted_inbox_root, got {other:?}"),
        }
    }

    #[test]
    fn dispute_count_decrement_rejected() {
        let p = strip_witness_constraints(relay_operator_program());
        let mut old = base_state();
        old.fields[DISPUTE_COUNT_SLOT as usize] = u64_field(3);
        let mut bad = old.clone();
        bad.fields[BOND_AMOUNT_SLOT as usize] = u64_field(5_000); // decrease
        bad.fields[DISPUTE_COUNT_SLOT as usize] = u64_field(2); // adversarial decrement
        let err = p
            .evaluate_with_meta(&bad, Some(&old), None, &method_meta("slash"))
            .expect_err("dispute_count rewind must be rejected");
        assert!(matches!(err, ProgramError::ConstraintViolated { .. }));
    }
}

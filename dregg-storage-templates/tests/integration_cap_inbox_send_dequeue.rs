//! Integration test: CapInbox composed send/dequeue flow.
//!
//! Drives the full `send → dequeue` lifecycle:
//!
//! 1. `send` N messages (head advances, message_root changes, deposits grow).
//! 2. Attempt a `dequeue` that also advances head — reject (Immutable on head
//!    during dequeue).
//! 3. Perform a legal `dequeue` series (tail catches up to head).
//! 4. Attempt `dequeue` beyond head (tail would exceed head; verifies MonotonicSequence
//!    only advances by exactly +1 and that we can't leapfrog).
//! 5. `grant_sender` must not advance head/tail/deposits.
//! 6. Unknown method is default-denied.

use dregg_app_framework::symbol;
use dregg_cell::StateConstraint;
use dregg_cell::program::{CellProgram, ProgramError, TransitionMeta};
use dregg_cell::state::{CellState, FieldElement};

use dregg_storage_templates::cap_inbox::{
    CAPACITY_SLOT, HEAD_SEQ_SLOT, MESSAGE_ROOT_SLOT, MIN_DEPOSIT_SLOT, OWNER_PK_HASH_SLOT,
    SENDER_SET_ROOT_SLOT, TAIL_SEQ_SLOT, TOTAL_DEPOSITS_SLOT, cap_inbox_program, initial_state,
};

// ── helpers ─────────────────────────────────────────────────────────────────

fn blake3_field(bytes: &[u8]) -> FieldElement {
    *blake3::hash(bytes).as_bytes()
}

fn u64_field(v: u64) -> FieldElement {
    let mut out = [0u8; 32];
    out[24..32].copy_from_slice(&v.to_be_bytes());
    out
}

fn u64_from_field(f: &FieldElement) -> u64 {
    u64::from_be_bytes(f[24..32].try_into().unwrap())
}

/// Strip executor-wired constraints so we exercise only slot-caveat shape.
fn strip_executor_constraints(p: CellProgram) -> CellProgram {
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

/// Build a fresh CellState from `initial_state` helper.
fn make_base_cell() -> CellState {
    let owner = blake3_field(b"owner-pk");
    let sender_set = blake3_field(b"senders-root");
    let fields = initial_state(8, 100, owner, sender_set);
    let mut s = CellState::new(0);
    for (i, f) in fields.iter().enumerate() {
        s.fields[i] = *f;
    }
    s.set_nonce(1);
    s
}

/// Apply a `send`: head+1, deposits grow, ring root changes.
fn apply_send(old: &CellState, deposit: u64, payload_tag: &[u8]) -> CellState {
    let mut s = old.clone();
    let head = u64_from_field(&s.fields[HEAD_SEQ_SLOT as usize]);
    let total = u64_from_field(&s.fields[TOTAL_DEPOSITS_SLOT as usize]);
    s.fields[HEAD_SEQ_SLOT as usize] = u64_field(head + 1);
    s.fields[TOTAL_DEPOSITS_SLOT as usize] = u64_field(total + deposit);
    s.fields[MESSAGE_ROOT_SLOT as usize] = blake3_field(
        &[
            &old.fields[MESSAGE_ROOT_SLOT as usize][..],
            &blake3_field(payload_tag)[..],
        ]
        .concat(),
    );
    s
}

/// Apply a `dequeue`: tail+1 (deposits may shrink on refund, but we keep
/// them unchanged here to focus on tail advancement).
fn apply_dequeue(old: &CellState) -> CellState {
    let mut s = old.clone();
    let tail = u64_from_field(&s.fields[TAIL_SEQ_SLOT as usize]);
    s.fields[TAIL_SEQ_SLOT as usize] = u64_field(tail + 1);
    s
}

// ── tests ────────────────────────────────────────────────────────────────────

#[test]
fn send_n_messages_head_advances() {
    let p = strip_executor_constraints(cap_inbox_program());
    let mut state = make_base_cell();

    for i in 0u64..4 {
        let new = apply_send(&state, 100, &[i as u8; 8]);
        let r = p.evaluate_with_meta(&new, Some(&state), None, &method_meta("send"));
        assert!(r.is_ok(), "send #{i} must pass: {r:?}");
        assert_eq!(
            u64_from_field(&new.fields[HEAD_SEQ_SLOT as usize]),
            i + 1,
            "head after send #{i} must be {}",
            i + 1
        );
        // tail must remain 0 throughout sends.
        assert_eq!(
            u64_from_field(&new.fields[TAIL_SEQ_SLOT as usize]),
            0,
            "tail must stay 0 during sends"
        );
        state = new;
    }
    assert_eq!(u64_from_field(&state.fields[HEAD_SEQ_SLOT as usize]), 4);
}

#[test]
fn send_without_message_root_change_rejected() {
    let p = strip_executor_constraints(cap_inbox_program());
    let old = make_base_cell();

    let mut bad = old.clone();
    bad.fields[HEAD_SEQ_SLOT as usize] = u64_field(1);
    bad.fields[TOTAL_DEPOSITS_SLOT as usize] = u64_field(100);

    let err = p
        .evaluate_with_meta(&bad, Some(&old), None, &method_meta("send"))
        .expect_err("send without message_root change must be rejected");
    match err {
        ProgramError::ConstraintViolated {
            constraint: StateConstraint::Immutable { index },
            ..
        } => assert_eq!(index, MESSAGE_ROOT_SLOT),
        other => panic!("expected negated Immutable on message_root, got {other:?}"),
    }
}

#[test]
fn dequeue_that_also_advances_head_rejected() {
    // During a `dequeue`, `HEAD_SEQ_SLOT` must be `Immutable`.
    let p = strip_executor_constraints(cap_inbox_program());

    let mut state = make_base_cell();
    state = apply_send(&state, 100, b"msg-0");
    state = apply_send(&state, 100, b"msg-1");

    // Build a dequeue that sneaks a head advance.
    let mut bad = apply_dequeue(&state);
    bad.fields[HEAD_SEQ_SLOT as usize] = u64_field(3); // head would advance

    let err = p
        .evaluate_with_meta(&bad, Some(&state), None, &method_meta("dequeue"))
        .expect_err("dequeue that advances head must be rejected");
    match err {
        ProgramError::ConstraintViolated {
            constraint: StateConstraint::Immutable { index },
            ..
        } => assert_eq!(index, HEAD_SEQ_SLOT),
        other => panic!("expected Immutable on head_seq, got {other:?}"),
    }
}

#[test]
fn dequeue_series_tail_catches_head() {
    let p = strip_executor_constraints(cap_inbox_program());

    // Send 3 messages.
    let mut state = make_base_cell();
    for i in 0u64..3 {
        state = apply_send(&state, 100, &[i as u8; 4]);
    }
    assert_eq!(u64_from_field(&state.fields[HEAD_SEQ_SLOT as usize]), 3);
    assert_eq!(u64_from_field(&state.fields[TAIL_SEQ_SLOT as usize]), 0);

    // Dequeue all 3.
    for i in 0u64..3 {
        let new = apply_dequeue(&state);
        let r = p.evaluate_with_meta(&new, Some(&state), None, &method_meta("dequeue"));
        assert!(r.is_ok(), "dequeue #{i} must pass: {r:?}");
        assert_eq!(
            u64_from_field(&new.fields[TAIL_SEQ_SLOT as usize]),
            i + 1,
            "tail after dequeue #{i} must be {}",
            i + 1
        );
        state = new;
    }

    // tail == head == 3.
    assert_eq!(u64_from_field(&state.fields[TAIL_SEQ_SLOT as usize]), 3);
    assert_eq!(u64_from_field(&state.fields[HEAD_SEQ_SLOT as usize]), 3);
}

#[test]
fn dequeue_that_decrements_tail_rejected() {
    // MonotonicSequence on tail means it must advance exactly +1.
    let p = strip_executor_constraints(cap_inbox_program());

    let mut state = make_base_cell();
    state = apply_send(&state, 100, b"msg-0");
    // Advance tail to 1 first.
    state = apply_dequeue(&state);
    assert_eq!(u64_from_field(&state.fields[TAIL_SEQ_SLOT as usize]), 1);

    // Now attempt to rewind tail.
    let mut bad = state.clone();
    bad.fields[TAIL_SEQ_SLOT as usize] = u64_field(0);

    let err = p
        .evaluate_with_meta(&bad, Some(&state), None, &method_meta("dequeue"))
        .expect_err("tail decrement must be rejected");
    assert!(
        matches!(err, ProgramError::ConstraintViolated { .. }),
        "expected ConstraintViolated, got {err:?}"
    );
}

#[test]
fn dequeue_past_head_rejected() {
    let p = strip_executor_constraints(cap_inbox_program());

    let mut state = make_base_cell();
    state = apply_send(&state, 100, b"msg-0");
    state = apply_dequeue(&state);

    let bad = apply_dequeue(&state);
    let err = p
        .evaluate_with_meta(&bad, Some(&state), None, &method_meta("dequeue"))
        .expect_err("tail must not advance past head");
    match err {
        ProgramError::ConstraintViolated {
            constraint:
                StateConstraint::FieldLteField {
                    left_index,
                    right_index,
                },
            ..
        } => {
            assert_eq!(left_index, TAIL_SEQ_SLOT);
            assert_eq!(right_index, HEAD_SEQ_SLOT);
        }
        other => panic!("expected FieldLteField tail_seq <= head_seq, got {other:?}"),
    }
}

#[test]
fn grant_sender_does_not_advance_head_or_tail_or_deposits() {
    let p = strip_executor_constraints(cap_inbox_program());
    let old = make_base_cell();

    // grant_sender: only sender_set_root changes.
    let mut new = old.clone();
    new.fields[SENDER_SET_ROOT_SLOT as usize] = blake3_field(b"expanded-set");

    let r = p.evaluate_with_meta(&new, Some(&old), None, &method_meta("grant_sender"));
    assert!(r.is_ok(), "legal grant_sender must pass: {r:?}");

    assert_eq!(
        new.fields[HEAD_SEQ_SLOT as usize],
        old.fields[HEAD_SEQ_SLOT as usize]
    );
    assert_eq!(
        new.fields[TAIL_SEQ_SLOT as usize],
        old.fields[TAIL_SEQ_SLOT as usize]
    );
    assert_eq!(
        new.fields[TOTAL_DEPOSITS_SLOT as usize],
        old.fields[TOTAL_DEPOSITS_SLOT as usize]
    );
}

#[test]
fn grant_sender_without_sender_root_change_rejected() {
    let p = strip_executor_constraints(cap_inbox_program());
    let old = make_base_cell();
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

#[test]
fn grant_sender_that_also_advances_head_rejected() {
    let p = strip_executor_constraints(cap_inbox_program());
    let old = make_base_cell();

    let mut bad = old.clone();
    bad.fields[SENDER_SET_ROOT_SLOT as usize] = blake3_field(b"expanded-set");
    bad.fields[HEAD_SEQ_SLOT as usize] = u64_field(1); // must be Immutable during grant_sender

    let err = p
        .evaluate_with_meta(&bad, Some(&old), None, &method_meta("grant_sender"))
        .expect_err("grant_sender advancing head must be rejected");
    match err {
        ProgramError::ConstraintViolated {
            constraint: StateConstraint::Immutable { index },
            ..
        } => assert_eq!(index, HEAD_SEQ_SLOT),
        other => panic!("expected Immutable on head_seq, got {other:?}"),
    }
}

#[test]
fn unknown_method_default_denied_inbox() {
    let p = strip_executor_constraints(cap_inbox_program());
    let old = make_base_cell();
    let new = apply_send(&old, 100, b"x");

    let err = p
        .evaluate_with_meta(&new, Some(&old), None, &method_meta("drain_all"))
        .expect_err("unknown method must be default-denied");
    assert!(
        matches!(err, ProgramError::NoTransitionCaseMatched),
        "expected NoTransitionCaseMatched, got {err:?}"
    );
}

#[test]
fn immutable_slots_never_change_across_full_lifecycle() {
    let p = strip_executor_constraints(cap_inbox_program());
    let start = make_base_cell();

    let after_send = apply_send(&start, 100, b"msg-0");
    let after_dequeue = apply_dequeue(&after_send);

    for (label, state, prev) in [
        ("send", &after_send, &start),
        ("dequeue", &after_dequeue, &after_send),
    ] {
        let r = p.evaluate_with_meta(state, Some(prev), None, &method_meta(label));
        assert!(r.is_ok(), "{label} must pass: {r:?}");

        assert_eq!(
            state.fields[CAPACITY_SLOT as usize], start.fields[CAPACITY_SLOT as usize],
            "{label}: capacity must be immutable"
        );
        assert_eq!(
            state.fields[MIN_DEPOSIT_SLOT as usize], start.fields[MIN_DEPOSIT_SLOT as usize],
            "{label}: min_deposit must be immutable"
        );
        assert_eq!(
            state.fields[OWNER_PK_HASH_SLOT as usize], start.fields[OWNER_PK_HASH_SLOT as usize],
            "{label}: owner_pk_hash must be immutable"
        );
    }
}

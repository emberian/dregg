//! Integration test: BlindedQueue multi-item round-trip.
//!
//! Drives `blinded_queue_program()` through the `CellProgram::evaluate_with_meta`
//! path for a composed `add`/`consume` flow:
//!
//! 1. Start from a valid initial state.
//! 2. Add N items (each advancing `commitment_count` exactly once and changing `commitments_root`).
//! 3. Verify the `commitment_count` advances sequentially.
//! 4. Attempt to add while falsely claiming `commitment_count` stayed flat — reject.
//! 5. Consume an item (nullifier grows; commitments side frozen).
//! 6. Attempt to consume while allowing `commitments_root` to change — reject.
//! 7. Attempt to consume more times than items were added (nullifier_count > commitment_count
//!    check lives in `consume_without_witness`, so we exercise the slot-caveat shape here).

use dregg_app_framework::symbol;
use dregg_cell::StateConstraint;
use dregg_cell::program::{CellProgram, ProgramError, TransitionMeta};
use dregg_cell::state::{CellState, FieldElement};

use dregg_storage_templates::blinded_queue::{
    BLINDED_QUEUE_SPEND_AIR_VK, CAPACITY_SLOT, COMMITMENT_COUNT_SLOT, COMMITMENTS_ROOT_SLOT,
    CONSUMER_PK_HASH_SLOT, NULLIFIER_COUNT_SLOT, NULLIFIER_ROOT_SLOT, QUEUE_ID_HASH_SLOT,
    SPEND_AIR_VK_COMMITMENT_SLOT, blinded_queue_program,
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

/// Strip constraints that require executor wiring (SenderAuthorized, Witnessed,
/// RateLimit, RateLimitBySum) so we can exercise slot-caveat shape purely.
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

fn base_state() -> CellState {
    let mut s = CellState::new(0);
    s.fields[CAPACITY_SLOT as usize] = u64_field(16);
    s.fields[CONSUMER_PK_HASH_SLOT as usize] = blake3_field(b"consumer-pk");
    s.fields[SPEND_AIR_VK_COMMITMENT_SLOT as usize] = BLINDED_QUEUE_SPEND_AIR_VK;
    s.fields[QUEUE_ID_HASH_SLOT as usize] = blake3_field(b"queue-id");
    // Dynamic slots start at zero (commitment_count, nullifier_count, roots).
    s.set_nonce(1);
    s
}

/// Apply one `add` transition: advance count + root.
fn apply_add(old: &CellState, commitment_tag: &[u8]) -> CellState {
    let mut s = old.clone();
    let count = u64_from_field(&s.fields[COMMITMENT_COUNT_SLOT as usize]);
    s.fields[COMMITMENT_COUNT_SLOT as usize] = u64_field(count + 1);
    // New root = blake3(old_root || item_commitment)
    s.fields[COMMITMENTS_ROOT_SLOT as usize] = blake3_field(
        &[
            &old.fields[COMMITMENTS_ROOT_SLOT as usize][..],
            &blake3_field(commitment_tag)[..],
        ]
        .concat(),
    );
    s
}

/// Apply one `consume` transition: advance nullifier count + root; commitments frozen.
fn apply_consume(old: &CellState, nullifier_tag: &[u8]) -> CellState {
    let mut s = old.clone();
    let nc = u64_from_field(&s.fields[NULLIFIER_COUNT_SLOT as usize]);
    s.fields[NULLIFIER_COUNT_SLOT as usize] = u64_field(nc + 1);
    s.fields[NULLIFIER_ROOT_SLOT as usize] = blake3_field(
        &[
            &old.fields[NULLIFIER_ROOT_SLOT as usize][..],
            &blake3_field(nullifier_tag)[..],
        ]
        .concat(),
    );
    s
}

// ── tests ────────────────────────────────────────────────────────────────────

#[test]
fn add_n_items_commitment_count_grows_monotonically() {
    let p = strip_executor_constraints(blinded_queue_program());
    let mut state = base_state();

    for i in 0u64..5 {
        let new = apply_add(&state, &[i as u8; 4]);
        let r = p.evaluate_with_meta(&new, Some(&state), None, &method_meta("add"));
        assert!(r.is_ok(), "add #{i} must pass: {r:?}");
        // Verify count really advanced.
        assert_eq!(
            u64_from_field(&new.fields[COMMITMENT_COUNT_SLOT as usize]),
            i + 1,
            "commitment_count after add #{i} must be {}",
            i + 1
        );
        state = new;
    }

    // Final state: commitment_count == 5, nullifier_count == 0.
    assert_eq!(
        u64_from_field(&state.fields[COMMITMENT_COUNT_SLOT as usize]),
        5
    );
    assert_eq!(
        u64_from_field(&state.fields[NULLIFIER_COUNT_SLOT as usize]),
        0
    );
}

#[test]
fn add_with_flat_count_rejected() {
    // An add whose commitment_count stays the same as before violates
    // MonotonicSequence on COMMITMENT_COUNT_SLOT.
    let p = strip_executor_constraints(blinded_queue_program());
    let old = base_state();
    // Build a state that changes the root but leaves the count unchanged.
    let mut bad = old.clone();
    bad.fields[COMMITMENTS_ROOT_SLOT as usize] = blake3_field(b"attacker-root");
    // commitment_count stays 0 — violates MonotonicSequence.
    let err = p
        .evaluate_with_meta(&bad, Some(&old), None, &method_meta("add"))
        .expect_err("add without count increment must be rejected");
    assert!(
        matches!(err, ProgramError::ConstraintViolated { .. }),
        "expected ConstraintViolated, got {err:?}"
    );
}

#[test]
fn add_without_commitments_root_change_rejected() {
    let p = strip_executor_constraints(blinded_queue_program());
    let old = base_state();

    let mut bad = old.clone();
    bad.fields[COMMITMENT_COUNT_SLOT as usize] = u64_field(1);

    let err = p
        .evaluate_with_meta(&bad, Some(&old), None, &method_meta("add"))
        .expect_err("add without commitments_root change must be rejected");
    match err {
        ProgramError::ConstraintViolated {
            constraint: StateConstraint::Immutable { index },
            ..
        } => assert_eq!(index, COMMITMENTS_ROOT_SLOT),
        other => panic!("expected negated Immutable on commitments_root, got {other:?}"),
    }
}

#[test]
fn consume_after_add_succeeds_and_commitments_side_frozen() {
    let p = strip_executor_constraints(blinded_queue_program());

    // Add 3 items.
    let mut state = base_state();
    for i in 0u64..3 {
        state = apply_add(&state, &[i as u8; 4]);
    }

    // Consume one item.
    let after_consume = apply_consume(&state, b"nullifier-0");
    let r = p.evaluate_with_meta(&after_consume, Some(&state), None, &method_meta("consume"));
    assert!(r.is_ok(), "legal consume must pass: {r:?}");

    // Verify: nullifier_count advanced, commitments side unchanged.
    assert_eq!(
        u64_from_field(&after_consume.fields[NULLIFIER_COUNT_SLOT as usize]),
        1
    );
    assert_eq!(
        after_consume.fields[COMMITMENT_COUNT_SLOT as usize],
        state.fields[COMMITMENT_COUNT_SLOT as usize],
        "commitment_count must be immutable during consume"
    );
    assert_eq!(
        after_consume.fields[COMMITMENTS_ROOT_SLOT as usize],
        state.fields[COMMITMENTS_ROOT_SLOT as usize],
        "commitments_root must be immutable during consume"
    );
}

#[test]
fn consume_that_mutates_commitments_root_rejected() {
    let p = strip_executor_constraints(blinded_queue_program());

    // Add 2 items.
    let mut state = base_state();
    state = apply_add(&state, b"item-0");
    state = apply_add(&state, b"item-1");

    // Attempt a consume that also changes commitments_root.
    let mut bad = apply_consume(&state, b"null-0");
    bad.fields[COMMITMENTS_ROOT_SLOT as usize] = blake3_field(b"attacker-mutation");

    let err = p
        .evaluate_with_meta(&bad, Some(&state), None, &method_meta("consume"))
        .expect_err("consume that mutates commitments_root must be rejected");
    match err {
        ProgramError::ConstraintViolated {
            constraint: StateConstraint::Immutable { index },
            ..
        } => assert_eq!(index, COMMITMENTS_ROOT_SLOT),
        other => panic!("expected Immutable on commitments_root, got {other:?}"),
    }
}

#[test]
fn consume_that_decrements_nullifier_count_rejected() {
    let p = strip_executor_constraints(blinded_queue_program());

    // Set up state with 2 consumed items.
    let mut state = base_state();
    state = apply_add(&state, b"item-0");
    state = apply_add(&state, b"item-1");
    state = apply_consume(&state, b"null-0");
    state = apply_consume(&state, b"null-1");

    // Attempt a "consume" that rolls back nullifier_count.
    let mut bad = state.clone();
    bad.fields[NULLIFIER_COUNT_SLOT as usize] = u64_field(1); // rewind!
    bad.fields[NULLIFIER_ROOT_SLOT as usize] = blake3_field(b"rewound");

    let err = p
        .evaluate_with_meta(&bad, Some(&state), None, &method_meta("consume"))
        .expect_err("nullifier_count decrement must be rejected");
    assert!(
        matches!(err, ProgramError::ConstraintViolated { .. }),
        "expected ConstraintViolated, got {err:?}"
    );
}

#[test]
fn consume_past_commitment_count_rejected() {
    let p = strip_executor_constraints(blinded_queue_program());

    let mut state = base_state();
    state = apply_add(&state, b"item-0");
    state = apply_consume(&state, b"null-0");

    let bad = apply_consume(&state, b"null-1");
    let err = p
        .evaluate_with_meta(&bad, Some(&state), None, &method_meta("consume"))
        .expect_err("nullifier_count must not exceed commitment_count");
    match err {
        ProgramError::ConstraintViolated {
            constraint:
                StateConstraint::FieldLteField {
                    left_index,
                    right_index,
                },
            ..
        } => {
            assert_eq!(left_index, NULLIFIER_COUNT_SLOT);
            assert_eq!(right_index, COMMITMENT_COUNT_SLOT);
        }
        other => {
            panic!("expected FieldLteField nullifier_count <= commitment_count, got {other:?}")
        }
    }
}

#[test]
fn immutable_slots_survive_add_and_consume_sequences() {
    // Verify that capacity / consumer_pk / spend_air_vk / queue_id never
    // change across a full add+consume lifecycle.
    let p = strip_executor_constraints(blinded_queue_program());
    let start = base_state();

    let after_add = apply_add(&start, b"item-0");
    let after_consume = apply_consume(&after_add, b"null-0");

    for (label, state, prev) in [
        ("add", &after_add, &start),
        ("consume", &after_consume, &after_add),
    ] {
        let r = p.evaluate_with_meta(state, Some(prev), None, &method_meta(label));
        assert!(r.is_ok(), "{label} must pass: {r:?}");

        // Immutable slots must still match the base state.
        assert_eq!(
            state.fields[CAPACITY_SLOT as usize], start.fields[CAPACITY_SLOT as usize],
            "{label}: capacity changed"
        );
        assert_eq!(
            state.fields[CONSUMER_PK_HASH_SLOT as usize],
            start.fields[CONSUMER_PK_HASH_SLOT as usize],
            "{label}: consumer_pk_hash changed"
        );
        assert_eq!(
            state.fields[SPEND_AIR_VK_COMMITMENT_SLOT as usize],
            start.fields[SPEND_AIR_VK_COMMITMENT_SLOT as usize],
            "{label}: spend_air_vk changed"
        );
        assert_eq!(
            state.fields[QUEUE_ID_HASH_SLOT as usize], start.fields[QUEUE_ID_HASH_SLOT as usize],
            "{label}: queue_id_hash changed"
        );
    }
}

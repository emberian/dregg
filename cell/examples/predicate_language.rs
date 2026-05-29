//! The dregg predicate language, by example (GitHub issue #1).
//!
//! dregg's "predicate as data" model is `CellProgram::Predicate(Vec<StateConstraint>)`:
//! the constraints are declared on a cell, and the executor evaluates them on every
//! state transition via `CellProgram::evaluate(new_state, old_state, ctx)` *before*
//! committing a turn. If any constraint fails, the transition is rejected.
//!
//! This file constructs real programs and runs them against accepting and rejecting
//! transitions — the same call the executor makes. It is an executable answer to
//! "what does the canonical predicate pattern look like, and where does it live?"
//!
//! Canonical locations (code, not docs):
//!   - `StateConstraint`        cell/src/program.rs  (the constraint vocabulary)
//!   - `CellProgram`            cell/src/program.rs  (None | Predicate | Cases | Circuit)
//!   - `CellProgram::evaluate`  cell/src/program.rs  (the per-transition check)
//!   - `CellState` (8 slots)    cell/src/state.rs
//!
//! Run:
//!   cargo run -p dregg-cell --example predicate_language

use dregg_cell::program::{CellProgram, SimpleStateConstraint, StateConstraint, field_from_u64};
use dregg_cell::state::CellState;

fn main() {
    audience_routing_exact();
    audience_routing_any_of();
    transition_constraints();
    println!("\nall predicate examples evaluated as expected.");
}

/// akapug's case: "drop messages where the audience field doesn't match self."
///
/// Model state slot 0 as the message's declared audience. The cell program
/// requires that slot to equal this cell's own id, so a write addressed to
/// anyone else fails `evaluate` and the executor rejects the turn.
fn audience_routing_exact() {
    let self_id = field_from_u64(0xA11CE);
    let program = CellProgram::Predicate(vec![StateConstraint::FieldEquals {
        index: 0,
        value: self_id,
    }]);

    // Accept: a message addressed to us.
    let mut ours = CellState::new(0);
    ours.fields[0] = self_id;
    assert!(program.evaluate(&ours, None, None).is_ok());

    // Reject: a message addressed to someone else.
    let mut theirs = CellState::new(0);
    theirs.fields[0] = field_from_u64(0xB0B);
    assert!(program.evaluate(&theirs, None, None).is_err());

    println!("[audience exact]   accept own-id, reject other-id");
}

/// "audience is one of N allowed recipients" — akapug's `AnyOf`-over-identities idea.
///
/// `AnyOf` is a single-level disjunction over `SimpleStateConstraint`s: the
/// transition passes if any branch holds.
fn audience_routing_any_of() {
    let alice = field_from_u64(0xA11CE);
    let bob = field_from_u64(0xB0B);
    let program = CellProgram::Predicate(vec![StateConstraint::AnyOf {
        variants: vec![
            SimpleStateConstraint::FieldEquals {
                index: 0,
                value: alice,
            },
            SimpleStateConstraint::FieldEquals {
                index: 0,
                value: bob,
            },
        ],
    }]);

    // Accept: addressed to one of the allowed recipients.
    let mut to_bob = CellState::new(0);
    to_bob.fields[0] = bob;
    assert!(program.evaluate(&to_bob, None, None).is_ok());

    // Reject: addressed to someone outside the set.
    let mut to_carol = CellState::new(0);
    to_carol.fields[0] = field_from_u64(0xCABE);
    assert!(program.evaluate(&to_carol, None, None).is_err());

    println!("[audience anyOf]   accept {{alice, bob}}, reject carol");
}

/// Transition constraints compare the new state against the old, so `evaluate`
/// is called with `Some(&old_state)`.
///   - `WriteOnce`: a slot may be set once (from zero), then never changed.
///   - `Monotonic`: a slot may only stay equal or increase.
fn transition_constraints() {
    let program = CellProgram::Predicate(vec![
        StateConstraint::WriteOnce { index: 1 },
        StateConstraint::Monotonic { index: 2 },
    ]);

    let mut old = CellState::new(0);
    old.fields[1] = field_from_u64(0); // slot 1 unset
    old.fields[2] = field_from_u64(10);

    // Accept: first write to the WriteOnce slot, and an increase of the Monotonic slot.
    let mut good = old.clone();
    good.fields[1] = field_from_u64(7);
    good.fields[2] = field_from_u64(20);
    assert!(program.evaluate(&good, Some(&old), None).is_ok());

    // Reject: decreasing the Monotonic slot.
    let mut down = old.clone();
    down.fields[2] = field_from_u64(5);
    assert!(program.evaluate(&down, Some(&old), None).is_err());

    // Reject: rewriting an already-set WriteOnce slot.
    let mut set = CellState::new(0);
    set.fields[1] = field_from_u64(7);
    let mut rewrite = set.clone();
    rewrite.fields[1] = field_from_u64(8);
    assert!(program.evaluate(&rewrite, Some(&set), None).is_err());

    println!("[writeonce/mono]   accept first-write & increase, reject rewrite & decrease");
}

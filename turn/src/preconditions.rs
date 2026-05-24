//! Ergonomic precondition builders for [`Action::preconditions`].
//!
//! The underlying [`pyana_cell::Preconditions`] struct is the canonical
//! shape — the executor reads it directly in
//! `TurnExecutor::check_preconditions`. This module exposes a small
//! enum-shaped builder API so app/userspace callers do not have to know
//! the field layout to express simple "see-then-set" guards.
//!
//! See `APPS-USERSPACE-GAPS.md` §Gap 2 for the design framing. The three
//! variants the gap calls out — `SlotEquals`, `SlotZero`,
//! `NonceAtLeast` — map straight to fields on the existing struct:
//!
//! | builder variant         | underlying field                    |
//! |-------------------------|-------------------------------------|
//! | `SlotEquals(idx, val)`  | `cell_state.field_equals.push(..)`  |
//! | `SlotZero(idx)`         | `cell_state.field_equals` with `[0u8; 32]` |
//! | `NonceAtLeast(n)`       | `cell_state.min_nonce = Some(n)`    |
//!
//! The verifier-side check lives in
//! `pyana_cell::CellStatePrecondition::evaluate`, which the executor
//! invokes from `TurnExecutor::check_preconditions` before applying any
//! effects in the action. Violations reject the action (returning the
//! corresponding [`pyana_cell::PreconditionError`]) before any state
//! mutation runs.

use pyana_cell::state::FieldElement;
use pyana_cell::{CellStatePrecondition, Preconditions};

/// A single see-then-set precondition.
///
/// Compose these into a [`Preconditions`] via [`build`] / [`extend`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Precondition {
    /// The cell's storage slot at `index` must equal `value`.
    SlotEquals { index: usize, value: FieldElement },
    /// The cell's storage slot at `index` must be zero (the all-zero
    /// `FieldElement`). Shorthand for `SlotEquals { index, value: [0; 32] }`.
    SlotZero { index: usize },
    /// The cell's `nonce` must be at least `min`. Use when an action
    /// needs monotonic-nonce semantics but cannot pin to an exact value
    /// (which would race against concurrent submitters).
    NonceAtLeast(u64),
}

impl Precondition {
    /// Apply this precondition onto a [`CellStatePrecondition`].
    pub fn apply(&self, cs: &mut CellStatePrecondition) {
        match *self {
            Precondition::SlotEquals { index, value } => {
                cs.field_equals.push((index, value));
            }
            Precondition::SlotZero { index } => {
                cs.field_equals.push((index, [0u8; 32]));
            }
            Precondition::NonceAtLeast(n) => {
                cs.min_nonce = Some(match cs.min_nonce {
                    Some(prev) => prev.max(n),
                    None => n,
                });
            }
        }
    }
}

/// Build a [`Preconditions`] from a slice of [`Precondition`]s.
pub fn build(items: &[Precondition]) -> Preconditions {
    let mut out = Preconditions::default();
    extend(&mut out, items);
    out
}

/// Extend an existing [`Preconditions`] with additional [`Precondition`]s.
pub fn extend(target: &mut Preconditions, items: &[Precondition]) {
    if items.is_empty() {
        return;
    }
    let cs = target.cell_state.get_or_insert_with(Default::default);
    for item in items {
        item.apply(cs);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_cell::EvalContext;
    use pyana_cell::state::CellState;

    fn state_with(nonce: u64, fields: &[(usize, FieldElement)]) -> CellState {
        let mut s = CellState::new(0);
        s.set_nonce(nonce);
        for &(i, v) in fields {
            assert!(s.set_field(i, v), "slot {i} must be within STATE_SLOTS");
        }
        s
    }

    fn ctx() -> EvalContext {
        EvalContext {
            block_height: 0,
            timestamp: 0,
            ..Default::default()
        }
    }

    #[test]
    fn slot_equals_pass_and_fail() {
        let value = [7u8; 32];
        let pre = build(&[Precondition::SlotEquals { index: 3, value }]);
        let state_ok = state_with(0, &[(3, value)]);
        assert!(pre.evaluate(&state_ok, &ctx()).is_ok());
        let state_bad = state_with(0, &[(3, [9u8; 32])]);
        assert!(pre.evaluate(&state_bad, &ctx()).is_err());
    }

    #[test]
    fn slot_zero_rejects_nonzero() {
        let pre = build(&[Precondition::SlotZero { index: 5 }]);
        let state_ok = state_with(0, &[(5, [0u8; 32])]);
        assert!(pre.evaluate(&state_ok, &ctx()).is_ok());
        let state_bad = state_with(0, &[(5, [1u8; 32])]);
        assert!(pre.evaluate(&state_bad, &ctx()).is_err());
    }

    #[test]
    fn nonce_at_least_pass_and_fail() {
        let pre = build(&[Precondition::NonceAtLeast(10)]);
        let state_ok = state_with(10, &[]);
        assert!(pre.evaluate(&state_ok, &ctx()).is_ok());
        let state_ok2 = state_with(11, &[]);
        assert!(pre.evaluate(&state_ok2, &ctx()).is_ok());
        let state_bad = state_with(9, &[]);
        assert!(pre.evaluate(&state_bad, &ctx()).is_err());
    }

    #[test]
    fn multiple_preconditions_combine() {
        let value = [3u8; 32];
        let pre = build(&[
            Precondition::SlotEquals { index: 2, value },
            Precondition::SlotZero { index: 4 },
            Precondition::NonceAtLeast(5),
        ]);
        let state_ok = state_with(7, &[(2, value), (4, [0u8; 32])]);
        assert!(pre.evaluate(&state_ok, &ctx()).is_ok());

        // Fail on nonce
        let state_bad_nonce = state_with(3, &[(2, value), (4, [0u8; 32])]);
        assert!(pre.evaluate(&state_bad_nonce, &ctx()).is_err());

        // Fail on slot equals
        let state_bad_slot = state_with(7, &[(2, [9u8; 32]), (4, [0u8; 32])]);
        assert!(pre.evaluate(&state_bad_slot, &ctx()).is_err());
    }

    #[test]
    fn nonce_at_least_takes_max_when_repeated() {
        let pre = build(&[Precondition::NonceAtLeast(3), Precondition::NonceAtLeast(7)]);
        let cs = pre.cell_state.as_ref().expect("cell_state present");
        assert_eq!(cs.min_nonce, Some(7));
    }
}

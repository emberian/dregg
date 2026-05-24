//! Ergonomic precondition builders for [`Action::preconditions`].
//!
//! Per PREDICATE-INVENTORY §4.3 case 1 + §7.5, the duplicate surface
//! between this module and `pyana_cell::preconditions` was collapsed.
//! The canonical clause enum and builder live in `pyana_cell` now;
//! this module re-exports them as
//! [`Precondition`] / [`build`] / [`extend`] so existing callers
//! compile unchanged, but the evaluator is the cell-side one
//! ([`pyana_cell::Preconditions::evaluate`]).
//!
//! ## What changed
//!
//! - `Precondition` is a thin re-export of `pyana_cell::PreconditionClause`,
//!   which adds a `Witnessed(WitnessedPredicate)` variant alongside
//!   the existing `SlotEquals`, `SlotZero`, `NonceAtLeast`.
//! - `build` / `extend` delegate to the cell-side
//!   [`pyana_cell::PreconditionsBuilder`] / [`pyana_cell::Preconditions::extend_clauses`].
//! - No parallel evaluator. The verifier-side check still lives in
//!   `pyana_cell::CellStatePrecondition::evaluate`, invoked from
//!   `TurnExecutor::check_preconditions` before any effects in the
//!   action are applied.

pub use pyana_cell::PreconditionClause as Precondition;
use pyana_cell::Preconditions;

/// Build a [`Preconditions`] from a slice of [`Precondition`]s.
pub fn build(items: &[Precondition]) -> Preconditions {
    Preconditions::builder().extend(items).build()
}

/// Extend an existing [`Preconditions`] with additional [`Precondition`]s.
pub fn extend(target: &mut Preconditions, items: &[Precondition]) {
    target.extend_clauses(items);
}

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_cell::EvalContext;
    use pyana_cell::state::{CellState, FieldElement};

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

    #[test]
    fn witnessed_clause_appends_to_witnessed_field() {
        use pyana_cell::{InputRef, WitnessedPredicate};
        let wp = WitnessedPredicate::dfa([1u8; 32], InputRef::Sender, 0);
        let pre = build(&[Precondition::Witnessed(wp.clone())]);
        assert_eq!(pre.witnessed.len(), 1);
        assert_eq!(pre.witnessed[0], wp);
    }
}

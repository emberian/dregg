//! Protocol invariant: `CellProgram::Predicate(Vec<_>)` is a conjunction.
//!
//! > For any list of constraints `cs` and any (old, new) state pair,
//! > `Predicate(cs).evaluate(...)` is `Ok` IFF every `c ∈ cs`
//! > individually evaluates to `Ok`.
//!
//! The dual: if any single conjunct rejects, the program rejects. This is
//! the foundational compositionality claim for slot caveats.
//!
//! Source: `SLOT-CAVEATS-EVALUATION.md` §4 + `cell/src/program.rs::CellProgram::evaluate_full`.

use crate::Invariant;
use proptest::prelude::*;
use dregg_cell::{CellProgram, CellState, StateConstraint, field_from_u64};

pub struct StateConstraintConjunction;
impl Invariant for StateConstraintConjunction {
    const NAME: &'static str = "state_constraint_conjunction";
    const DESCRIPTION: &'static str =
        "CellProgram::Predicate(cs).evaluate is Ok iff every c in cs is individually Ok";
}

// Strategy: pick 1..=4 simple constraints over the same single slot to
// bound the matrix; this is sufficient to exercise the conjunction
// behavior without combinatorial blowup.
fn arb_field_equals_set() -> impl Strategy<Value = Vec<StateConstraint>> {
    proptest::collection::vec(0u64..16, 1..=4).prop_map(|vs| {
        vs.into_iter()
            .map(|v| StateConstraint::FieldEquals {
                index: 0,
                value: field_from_u64(v),
            })
            .collect()
    })
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(200))]

    /// For any conjunction of FieldEquals constraints over slot 0 and any
    /// concrete slot value `v`, the program accepts iff every constraint's
    /// expected value equals `v`.
    #[test]
    fn conjunction_equals_distributes_over_individual_check(
        cs in arb_field_equals_set(),
        v in 0u64..16,
    ) {
        let mut state = CellState::default();
        state.fields[0] = field_from_u64(v);

        let program_ok = CellProgram::Predicate(cs.clone())
            .evaluate(&state, None, None)
            .is_ok();

        let all_individual_ok = cs.iter().all(|c| {
            CellProgram::Predicate(vec![c.clone()])
                .evaluate(&state, None, None)
                .is_ok()
        });

        prop_assert_eq!(
            program_ok,
            all_individual_ok,
            "conjunction must equal universal individual; cs={:?}, v={}",
            cs,
            v
        );
    }
}

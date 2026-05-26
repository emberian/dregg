//! Protocol invariant: `StateConstraint::AnyOf { variants }` is a single-
//! level disjunction over `SimpleStateConstraint`.
//!
//! > `AnyOf { variants }` accepts a transition iff at least one variant
//! > in the list accepts it individually (when lifted to the full enum).
//!
//! Per `SLOT-CAVEATS-EVALUATION.md` §4.3 the lift is structurally
//! restricted: no nested `AnyOf`, no `Custom`. So the proof matrix is
//! bounded by `SimpleStateConstraint`'s closed enum.

use crate::Invariant;
use proptest::prelude::*;
use dregg_cell::{CellProgram, CellState, StateConstraint, field_from_u64};
use dregg_cell::program::SimpleStateConstraint;

pub struct AnyOfDisjunction;
impl Invariant for AnyOfDisjunction {
    const NAME: &'static str = "any_of_disjunction";
    const DESCRIPTION: &'static str =
        "AnyOf accepts a transition iff at least one inner variant accepts it";
}

fn arb_simple_field_equals_set() -> impl Strategy<Value = Vec<SimpleStateConstraint>> {
    proptest::collection::vec(0u64..16, 1..=4).prop_map(|vs| {
        vs.into_iter()
            .map(|v| SimpleStateConstraint::FieldEquals {
                index: 0,
                value: field_from_u64(v),
            })
            .collect()
    })
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(200))]

    #[test]
    fn any_of_accepts_iff_some_variant_holds(
        variants in arb_simple_field_equals_set(),
        v in 0u64..16,
    ) {
        let mut state = CellState::default();
        state.fields[0] = field_from_u64(v);
        let p = CellProgram::Predicate(vec![StateConstraint::AnyOf {
            variants: variants.clone(),
        }]);
        let program_ok = p.evaluate(&state, None, None).is_ok();

        // "At least one variant accepts" — compute by direct match on the
        // FieldEquals shape (the only shape this strategy produces).
        let any_individual_ok = variants.iter().any(|sv| match sv {
            SimpleStateConstraint::FieldEquals {
                index: 0,
                value,
            } => *value == field_from_u64(v),
            _ => false,
        });

        prop_assert_eq!(
            program_ok,
            any_individual_ok,
            "AnyOf accept != exists-individual-accept; variants={:?}, v={}",
            variants,
            v
        );
    }
}

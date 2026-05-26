//! Protocol invariant: sentinel-rejected `StateConstraint` variants.
//!
//! Per CAVEAT-LAYER-COVERAGE.md §6.1 / top-5 #1, four variants
//! (`TemporalPredicate`, `BoundDelta`, `Witnessed`, `Custom`) propagate
//! sentinel errors from the cell-side evaluator. Any `Predicate(_)` that
//! contains one of them must currently reject *every* transition (since
//! the executor surfaces the sentinel as `TurnError::ProgramViolation`).
//!
//! This invariant DOCUMENTS the current state so any code change that
//! flips it without intent is caught. When the caveat-correctness lane
//! lands the registry dispatch, the invariant must be **inverted or
//! retired** — flag the failure and update the test as the lane lands.

use crate::Invariant;
use proptest::prelude::*;

pub struct SentinelVariantsReject;
impl Invariant for SentinelVariantsReject {
    const NAME: &'static str = "sentinel_variants_reject";
    const DESCRIPTION: &'static str = "TemporalPredicate, BoundDelta, Witnessed, Custom — cell-side evaluator rejects unconditionally (current substrate state per CAVEAT-LAYER-COVERAGE.md §6.1)";
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    /// For any state, declaring a `TemporalPredicate` variant in a
    /// `Predicate(...)` makes the program reject.
    #[test]
    fn temporal_predicate_variant_always_rejects(state_seed in 0u64..256) {
        let mut state = CellState::default();
        state.fields[0] = dregg_cell::field_from_u64(state_seed);
        let p = CellProgram::Predicate(vec![StateConstraint::TemporalPredicate {
            witness_index: 0,
            dsl_hash: [0u8; 32],
        }]);
        prop_assert!(p.evaluate(&state, None, None).is_err());
    }

    #[test]
    fn bound_delta_variant_always_rejects(state_seed in 0u64..256, peer_seed in 0u8..255) {
        let mut state = CellState::default();
        state.fields[0] = dregg_cell::field_from_u64(state_seed);
        let p = CellProgram::Predicate(vec![StateConstraint::BoundDelta {
            local_slot: 0,
            peer_cell: CellId([peer_seed; 32]),
            peer_slot: 0,
            delta_relation: DeltaRelation::EqualAndOpposite,
        }]);
        prop_assert!(p.evaluate(&state, None, None).is_err());
    }

    #[test]
    fn witnessed_variant_always_rejects(state_seed in 0u64..256, commit_seed in 0u8..255) {
        let mut state = CellState::default();
        state.fields[0] = dregg_cell::field_from_u64(state_seed);
        let p = CellProgram::Predicate(vec![StateConstraint::Witnessed {
            wp: WitnessedPredicate::dfa([commit_seed; 32], InputRef::Sender, 0),
        }]);
        prop_assert!(p.evaluate(&state, None, None).is_err());
    }

    #[test]
    fn custom_variant_always_rejects(state_seed in 0u64..256, ir_seed in 0u8..255) {
        let mut state = CellState::default();
        state.fields[0] = dregg_cell::field_from_u64(state_seed);
        let p = CellProgram::Predicate(vec![StateConstraint::Custom {
            ir_hash: [ir_seed; 32],
            descriptor: CustomDescriptor::default(),
            reads: ReadSet::default(),
        }]);
        prop_assert!(p.evaluate(&state, None, None).is_err());
    }
}

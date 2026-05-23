//! Temporal predicate AIR -- backward-compatible stub.
//!
//! The production temporal predicate implementation lives in
//! [`crate::temporal_predicate_dsl`]. This module provides the p3_temporal
//! submodule for Plonky3-native temporal proofs.

/// Plonky3-native temporal predicate AIR.
#[cfg(feature = "plonky3")]
pub mod p3_temporal {
    use crate::field::BabyBear;
    use crate::plonky3_prover::{PyanaProof, create_config, to_p3, trace_to_matrix};
    use crate::predicate_air::PREDICATE_DIFF_BITS;

    use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
    use p3_baby_bear::BabyBear as P3BabyBear;
    use p3_field::{PrimeCharacteristicRing, PrimeField32};

    pub const P3_TEMPORAL_WIDTH: usize = 36;

    pub mod col {
        pub const VALUE: usize = 0;
        pub const THRESHOLD: usize = 1;
        pub const DIFF: usize = 2;
        pub const DIFF_BITS_START: usize = 3;
        pub const ACCUMULATOR: usize = 33;
        pub const STATE_ROOT: usize = 34;
        pub const FACT_COMMITMENT: usize = 35;
    }

    pub struct P3TemporalPredicateAir {
        pub num_steps: usize,
    }

    impl P3TemporalPredicateAir {
        pub fn new(num_steps: usize) -> Self {
            Self { num_steps }
        }
    }

    #[derive(Clone, Debug)]
    pub struct P3TemporalPredicateProof {
        pub proof: PyanaProof,
        pub num_steps: usize,
    }

    pub fn prove_temporal_predicate_p3(
        values: &[BabyBear],
        state_roots: &[BabyBear],
        predicate_type: crate::predicate_air::PredicateType,
        threshold: u32,
    ) -> Result<P3TemporalPredicateProof, String> {
        Err("p3_temporal proving not yet migrated to DSL".into())
    }

    pub fn verify_temporal_predicate_p3(
        proof: &P3TemporalPredicateProof,
        num_steps: usize,
    ) -> Result<(), String> {
        Err("p3_temporal verification not yet migrated to DSL".into())
    }
}

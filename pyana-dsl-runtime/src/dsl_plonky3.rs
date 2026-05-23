//! Plonky3-backed DSL circuit proving via the native AIR interface.
//!
//! Provides a `StarkAir` wrapper (`DslP3Air`) around `CircuitDescriptor` so that
//! DSL-generated circuits can be proved/verified using the Plonky3 backend.

use crate::circuit::CircuitDescriptor;
use pyana_circuit::field::BabyBear;
use pyana_circuit::stark::{self, StarkAir, StarkProof};

/// A StarkAir implementation driven by a CircuitDescriptor.
///
/// This wraps a DSL-generated circuit descriptor and implements the `StarkAir` trait
/// so it can be proved using `stark::prove()` and verified using `stark::verify()`.
pub struct DslP3Air {
    descriptor: CircuitDescriptor,
}

impl DslP3Air {
    /// Create a new DslP3Air from a circuit descriptor.
    pub fn new(descriptor: CircuitDescriptor) -> Self {
        Self { descriptor }
    }

    /// Get the underlying descriptor.
    pub fn descriptor(&self) -> &CircuitDescriptor {
        &self.descriptor
    }
}

impl StarkAir for DslP3Air {
    fn width(&self) -> usize {
        self.descriptor.trace_width()
    }

    fn eval_constraints(
        &self,
        local: &[BabyBear],
        next: &[BabyBear],
        public_inputs: &[BabyBear],
        alpha: BabyBear,
    ) -> BabyBear {
        self.descriptor
            .eval_constraints_combined(local, next, public_inputs, alpha)
    }

    fn constraint_degree(&self) -> usize {
        self.descriptor.max_constraint_degree()
    }

    fn has_chain_continuity(&self) -> bool {
        false
    }

    fn air_name(&self) -> &'static str {
        "dsl-p3-circuit-v1"
    }
}

/// Prove a DSL circuit using the Plonky3-style STARK backend.
///
/// Takes a circuit descriptor, generates the trace, and produces a STARK proof.
pub fn prove_dsl_plonky3(
    descriptor: &CircuitDescriptor,
    trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
) -> StarkProof {
    let air = DslP3Air::new(descriptor.clone());
    stark::prove(&air, trace, public_inputs)
}

/// Verify a DSL circuit proof using the Plonky3-style STARK backend.
pub fn verify_dsl_plonky3(
    descriptor: &CircuitDescriptor,
    proof: &StarkProof,
    public_inputs: &[BabyBear],
) -> Result<(), String> {
    let air = DslP3Air::new(descriptor.clone());
    stark::verify(&air, proof, public_inputs)
}

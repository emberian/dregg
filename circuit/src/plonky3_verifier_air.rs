//! Plonky3 recursive verifier AIR -- stub module.
//!
//! Real recursive verification is not yet implemented. This module provides
//! the types needed by `ivc::recursive_ivc`.

use crate::field::BabyBear;
use crate::plonky3_prover::PyanaProof;

/// Recursion strategy selection.
pub enum RecursionMode {
    /// Use hash-chain accumulation (existing behavior, fast but weaker).
    HashChain,
    /// Request recursive STARK verification (currently unavailable).
    Recursive,
}

/// An IVC step proof using recursive verification.
pub struct RecursiveIvcStep {
    pub proof: PyanaProof,
    pub public_inputs: Vec<BabyBear>,
    pub step_number: u32,
}

/// Build a recursive IVC chain (currently unavailable).
pub fn build_recursive_ivc_chain(
    _fold_proofs: &[(&PyanaProof, &[BabyBear])],
) -> Result<RecursiveIvcStep, String> {
    Err(
        "recursive verification is unavailable: RecursiveVerifierAir is a non-functional placeholder"
            .to_string(),
    )
}

//! `dregg-circuit`: Zero-knowledge proof circuits for dregg authorization token chains.
//!
//! # Trust Model
//!
//! This crate operates at the **TRUSTLESS** trust level.
//!
//! - **Soundness**: All proofs are independently verifiable by any party with access to
//!   the public inputs and verification key. A valid proof guarantees that the prover
//!   knows a witness satisfying the circuit constraints, with negligible soundness error
//!   (2^{-128} for STARK, conjectured for Plonky3).
//! - **Assumptions**: Cryptographic hardness of the hash function (BLAKE3/Poseidon2),
//!   correct circuit constraint encoding, and honest verifier randomness (Fiat-Shamir).
//!   No trust in any federation member, operator, or third party.
//! - **Verifiable by**: Anyone. Proofs are publicly verifiable with O(log n) verification
//!   time. Light clients, external auditors, and cross-federation peers can all verify
//!   independently.
//!
//! All code in this crate MUST maintain the property that a valid proof implies a valid
//! witness. Bugs here break the entire trust model -- a soundness bug allows forged
//! authorization tokens.
//!
//! This crate implements the circuit layer for the dregg ZK token system,
//! proving: "I hold a valid attenuated token chain whose final state authorizes
//! action X" without revealing the chain or capabilities.
//!
//! # Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────────────┐
//! │                     Presentation Proof                               │
//! │                                                                     │
//! │  ┌──────────────┐   ┌──────────────┐         ┌──────────────┐     │
//! │  │  Fold AIR #1 │──▶│  Fold AIR #2 │──▶ ... ─▶│  Fold AIR #N │     │
//! │  │  (attenuation)│   │  (attenuation)│         │  (attenuation)│     │
//! │  └──────────────┘   └──────────────┘         └──────────────┘     │
//! │         │                                            │             │
//! │         │           initial_root                 final_root        │
//! │         │                                            │             │
//! │         ▼                                            ▼             │
//! │  ┌──────────────┐                          ┌──────────────┐      │
//! │  │ Merkle AIR   │                          │Derivation AIR│      │
//! │  │ (issuer key) │                          │(authorization)│      │
//! │  └──────────────┘                          └──────────────┘      │
//! │         │                                                         │
//! │         ▼                                                         │
//! │  federation_root                                                  │
//! └─────────────────────────────────────────────────────────────────────┘
//!
//! Public Inputs: [federation_root, request_predicate, timestamp]
//! Private Witness: [token_chain, derivation_trace, issuer_key]
//! ```
//!
//! # Features
//!
//! - `mock` (default): Uses a constraint satisfaction checker that evaluates
//!   AIR constraints directly without generating real STARK proofs.
//!   This validates circuit correctness and is suitable for development/testing.
//!
//! - `plonky3` (optional): Plonky3 dependencies available for future optimized prover.
//!
//! # Proof Backends
//!
//! - [`stark`]: Real STARK proof generation with FRI-based polynomial commitment.
//!   Produces actual cryptographic proofs (~24 KiB for a 4-level Merkle membership).
//!   Uses BLAKE3 Merkle trees, Fiat-Shamir transform, and Reed-Solomon encoding.
//! - [`constraint_prover`]: Constraint satisfaction checker that validates circuit
//!   logic by evaluating AIR constraints directly on the execution trace.
//!
//! # Security Properties
//!
//! The circuit enforces:
//! 1. **Fact membership**: Every referenced fact exists in the committed Merkle tree.
//! 2. **Valid narrowing**: Each attenuation step only removes facts or adds checks.
//! 3. **Derivation correctness**: The authorization follows from the final state via valid rules.
//! 4. **Issuer accountability**: The token chain originates from a federated issuer.
//! 5. **Freshness**: The proof is bound to a specific timestamp.
//!
//! # Components
//!
//! - [`field`]: BabyBear field arithmetic (p = 2^31 - 1).
//! - [`poseidon2`]: SNARK-friendly hash function for in-circuit hashing.
//! - [`merkle_air`]: 4-ary Merkle membership proof circuit.
//! - [`derivation_air`]: Single Datalog derivation step circuit.
//! - [`fold_air`]: Attenuation (fold) step circuit.
//! - [`presentation`]: Complete presentation proof combining all pieces.
//! - [`constraint_prover`]: Constraint satisfaction evaluator.
//! - [`stark`]: Real STARK prover/verifier (FRI + Merkle + Fiat-Shamir).

pub mod air_descriptor;
pub mod babybear8;
pub mod binding;
pub mod body_membership;
pub mod chunked_derivation;
pub mod constraint_prover;
#[allow(deprecated)]
pub mod cross_state_derivation;
pub mod dsl;
pub mod field;
pub mod ivc;

// Shared accumulator types used by both DSL and non-membership modules.
pub mod accumulator_types;

// Backward-compatible shim modules (type definitions + re-exports from DSL).
// These contain deprecated StarkAir impls superseded by DSL descriptors.
pub mod arithmetic_predicate_air;
pub mod block_transition_air;
pub mod bridge_action_air;
pub mod bridge_lock_action_air;
pub mod compound_predicate_air;
#[allow(deprecated)]
pub mod derivation_air;
pub mod effect_action_air;
pub mod fold_air;
pub mod fold_types;
#[allow(deprecated)]
pub mod garbled_air;
pub mod merkle_air;
pub mod merkle_types;
#[allow(deprecated)]
pub mod multi_step_air;
pub mod native_signature_air;
#[allow(deprecated)]
pub mod note_spending_air;
#[allow(deprecated)]
pub mod poseidon2_air;
pub mod predicate_air;
pub mod relational_predicate_air;
pub mod schnorr_air;
#[cfg(feature = "plonky3")]
pub mod temporal_predicate_air;

/// Backward-compatible re-export. Prefer [`constraint_prover`] for new code.
#[doc(hidden)]
pub mod mock_prover {
    pub use crate::constraint_prover::*;
}
pub mod poseidon2;
#[allow(deprecated)]
pub mod presentation;

#[allow(deprecated)]
pub mod committed_threshold;
pub mod effect_interp;
pub mod effect_vm;
#[allow(deprecated)]
pub mod garbled;
pub mod native_signature;
#[allow(deprecated)]
pub mod non_membership;
pub mod predicate_program;
#[allow(deprecated)]
pub mod quantified_absence;
pub mod schnorr_curve;
pub mod schnorr_sig;
pub mod stark;

#[cfg(feature = "mina")]
pub mod poseidon_stark;
#[cfg(feature = "mina")]
pub mod poseidon_stark_verifier_circuit;
pub mod temporal_predicate_dsl;

#[cfg(feature = "plonky3")]
pub mod plonky3_prover;

#[cfg(feature = "plonky3")]
pub mod plonky3_recursion;

#[cfg(feature = "plonky3")]
pub mod plonky3_verifier_air;

#[cfg(feature = "recursion")]
pub mod plonky3_recursion_impl;

/// Recursive (Golden Vision) compression bridge for `dregg_turn::WitnessedReceipt`
/// scope-2 replay. See the module docs for the Silver→Golden mapping and
/// the VK v2 layered encoding of the recursive VK hash.
#[cfg(feature = "recursion")]
pub mod recursive_witness_bundle;

/// Stage 7-γ.2 Phase 2 joint bilateral aggregation AIR. Consumes N per-cell
/// γ.2 PI vectors and the schedule-derived projection; emits a single outer
/// proof attesting bilateral consistency. See module docs and
/// `STAGE-7-GAMMA-2-PHASE-2-SKETCH.md`.
pub mod bilateral_aggregation_air;

/// Effect-VM-shape bridge AIR for the `p3-recursion` path. See module
/// docs — this is a *shape* mirror of `effect_vm::EffectVmAir` used to
/// measure that the recursion library accepts the Effect VM's column and
/// PI counts (Block 1/2 of the Golden Vision recursion lane).
#[cfg(feature = "recursion")]
pub mod effect_vm_p3_air;

pub mod backends;
pub mod proof_tier;

#[cfg(test)]
#[allow(deprecated)]
mod tests;

#[cfg(test)]
#[allow(deprecated)]
mod soundness_tests;

// Proof tier types — prevents scaffold/test proofs from satisfying production verifiers.
pub use proof_tier::{CryptographicProof, ProofTier, VerifiedProof};

// Re-export primary types.
pub use binding::{
    ACTION_BINDING_WIDTH, ActionBinding, PRESENTATION_TAG_WIDTH, PresentationTag, WideHash,
    compute_action_binding, compute_action_binding_narrow, compute_presentation_tag,
    compute_presentation_tag_narrow,
};
pub use body_membership::{
    BodyFactMerkleProof, BodyMembershipProof, MembershipEntry, collect_body_fact_hashes,
    prove_authorization_with_membership, verify_authorization_with_membership,
};
pub use chunked_derivation::{
    ChunkedAuthorizationProof, DEFAULT_CHUNK_SIZE, prove_chunked_authorization,
    verify_chunked_authorization,
};
#[allow(deprecated)]
pub use committed_threshold::{
    CommittedThresholdAir, CommittedThresholdProof, CommittedThresholdWitness,
    compute_threshold_commitment, generate_blinding, prove_committed_threshold,
    verify_committed_threshold,
};
#[doc(hidden)]
pub use constraint_prover::MockProof;
#[doc(hidden)]
pub use constraint_prover::MockProofResult;
#[doc(hidden)]
pub use constraint_prover::MockProver;
pub use constraint_prover::{
    Air, ConstraintCheckResult, ConstraintProof, ConstraintProver, ConstraintViolation,
};
pub use cross_state_derivation::{
    CombiningRule, CrossStateDerivationProof, SourceDerivation, SourceInput,
    prove_cross_state_derivation, verify_cross_state_derivation,
};
pub use effect_vm::{
    CellState, EFFECT_VM_WIDTH, Effect, EffectVmAir, NUM_EFFECTS, compute_effects_hash,
    encode_net_delta, extract_custom_proof_commitments, extract_net_delta,
    generate_effect_vm_trace, verify_balance_limb_pis,
};
pub use field::BabyBear;
pub use ivc::{
    FoldDelta, FoldMembershipEntry, FoldStepWitness, IvcBackend, IvcBackendProof, IvcBuilder,
    IvcPresentationProof, IvcProof, IvcVerification, MAX_FOLD_DEPTH, StateTransitionAir,
    ValidatedIvcProof, ValidatedIvcVerification, prove_ivc, prove_ivc_stark, prove_validated_ivc,
    verify_ivc, verify_ivc_stark, verify_validated_ivc,
};
pub use non_membership::{
    AugmentedDerivation, DerivationNonMembershipCheck, NonMembershipCheck, NonMembershipProof,
    NonMembershipProver, SetIdentifier, compute_set_accumulator, derive_alpha_for_set,
    verify_augmented_derivation, verify_non_membership_proof,
};
pub use presentation::{
    AuthorizationProof, PresentationAir, PresentationProof, PresentationVerification,
    PresentationWitness, RealPresentationProof, prove_authorization,
};
// Re-export predicate types at crate root for backward compatibility.
pub use predicate_air::{
    PredicateAir, PredicateProof, PredicateType, PredicateWitness, compute_fact_commitment,
    prove_in_range, prove_predicate, verify_in_range, verify_predicate,
};

// Re-export arithmetic predicate types at crate root.
pub use arithmetic_predicate_air::{
    ArithExpr, ArithPredicate, ArithmeticPredicateProof, ArithmeticPredicateWitness, CompareOp,
    compute_arithmetic_fact_commitment, prove_arithmetic_dsl, prove_arithmetic_predicate,
    verify_arithmetic_dsl, verify_arithmetic_predicate,
};

// Re-export relational predicate types at crate root.
pub use relational_predicate_air::{
    RelationType, RelationalPredicateProof, RelationalPredicateWitness, RelationalProof,
    RelationalWitness, compute_value_commitment, prove_relational, prove_value_comparison,
    verify_relational,
};

// Re-export multi-step authorization proving functions.
pub use multi_step_air::{
    MAX_DELEGATION_DEPTH, prove_authorization_stark, try_prove_authorization_stark,
};

/// Backward-compatible module alias for predicate types.
pub mod predicate_types {
    pub use crate::arithmetic_predicate_air::*;
    pub use crate::dsl::predicates::compute_blinded_fact_commitment;
    pub use crate::predicate_air::*;
    pub use crate::relational_predicate_air::*;
}

// Schnorr signature scheme over BabyBear^8 elliptic curve.
pub use babybear8::BabyBear8;
pub use schnorr_curve::{CurvePoint, GENERATOR as SCHNORR_GENERATOR};
pub use schnorr_sig::{
    SchnorrPublicKey, SchnorrSecretKey, SchnorrSignature, compress_public_key, schnorr_keygen,
    schnorr_sign, schnorr_verify,
};

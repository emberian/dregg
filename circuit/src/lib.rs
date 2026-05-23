//! `pyana-circuit`: Zero-knowledge proof circuits for pyana authorization token chains.
//!
//! This crate implements the circuit layer for the pyana ZK token system,
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

pub mod babybear8;
pub mod binding;
pub mod body_membership;
pub mod chunked_derivation;
pub mod constraint_prover;
pub mod cross_state_derivation;
pub mod derivation_air;
pub mod field;
pub mod fold_air;
pub mod ivc;
pub mod merkle_air;

/// Backward-compatible re-export. Prefer [`constraint_prover`] for new code.
#[doc(hidden)]
pub mod mock_prover {
    pub use crate::constraint_prover::*;
}
pub mod multi_step_air;
pub mod poseidon2;
pub mod poseidon2_air;
pub mod presentation;

pub mod accumulator_air;
pub mod arithmetic_predicate_air;
pub mod block_transition_air;
pub mod committed_threshold;
pub mod compound_predicate_air;
pub mod garbled;
pub mod garbled_air;
pub mod non_membership;
pub mod non_revocation_air;
pub mod note_spending_air;
pub mod predicate_air;
pub mod predicate_program;
pub mod quantified_absence;
pub mod relational_predicate_air;
pub mod schnorr_air;
pub mod schnorr_curve;
pub mod schnorr_sig;
pub mod sovereign_transition_air;
pub mod stark;
pub mod temporal_absence_air;

#[cfg(feature = "mina")]
pub mod poseidon_stark;
#[cfg(feature = "mina")]
pub mod poseidon_stark_verifier_circuit;
pub mod temporal_predicate_air;
pub mod temporal_predicate_dsl;
pub mod turn_validity_air;

#[cfg(feature = "plonky3")]
pub mod plonky3_prover;

#[cfg(feature = "plonky3")]
pub mod plonky3_recursion;

#[cfg(feature = "plonky3")]
pub mod plonky3_verifier_air;

#[cfg(feature = "recursion")]
pub mod plonky3_recursion_impl;

pub mod backends;
pub mod proof_tier;

#[cfg(test)]
mod tests;

// Proof tier types — prevents scaffold/test proofs from satisfying production verifiers.
pub use proof_tier::{CryptographicProof, ProofTier, VerifiedProof};

// Re-export primary types.
pub use body_membership::{
    BodyFactMerkleProof, BodyMembershipProof, MembershipEntry, collect_body_fact_hashes,
    prove_authorization_with_membership, verify_authorization_with_membership,
};
pub use constraint_prover::{
    Air, ConstraintCheckResult, ConstraintProof, ConstraintProver, ConstraintViolation,
};
pub use field::BabyBear;
pub use ivc::{
    FoldDelta, FoldMembershipEntry, FoldStepWitness, IvcBackend, IvcBackendProof, IvcBuilder,
    IvcPresentationProof, IvcProof, IvcVerification, MAX_FOLD_DEPTH, StateTransitionAir,
    ValidatedIvcProof, ValidatedIvcVerification, prove_ivc, prove_ivc_stark, prove_validated_ivc,
    verify_ivc, verify_ivc_stark, verify_validated_ivc,
};

// Backward-compatible aliases (hidden from docs).
pub use accumulator_air::{
    AccumulatorNonMembershipWitness, AccumulatorNonRevocationAir, AccumulatorNonRevocationWitness,
    ExtElem, compute_accumulator, derive_alpha, prove_accumulator_non_revocation,
    verify_accumulator_non_revocation,
};
pub use arithmetic_predicate_air::{
    ArithExpr, ArithPredicate, ArithmeticPredicateAir, ArithmeticPredicateProof,
    ArithmeticPredicateWitness, CompareOp, CompiledArith, compile_expression,
    compute_arithmetic_fact_commitment, evaluate_expression, prove_arithmetic_predicate,
    verify_arithmetic_predicate,
};
pub use binding::{
    ACTION_BINDING_WIDTH, ActionBinding, PRESENTATION_TAG_WIDTH, PresentationTag, WideHash,
    compute_action_binding, compute_action_binding_narrow, compute_presentation_tag,
    compute_presentation_tag_narrow,
};
pub use block_transition_air::{
    BlockEvent, BlockTransitionAir, BlockTransitionProof, MerkleUpdateWitness,
    prove_block_transition, verify_block_transition,
};
pub use chunked_derivation::{
    ChunkedAuthorizationProof, DEFAULT_CHUNK_SIZE, prove_chunked_authorization,
    verify_chunked_authorization,
};
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
pub use cross_state_derivation::{
    CombiningRule, CrossStateDerivationProof, SourceDerivation, SourceInput,
    prove_cross_state_derivation, verify_cross_state_derivation,
};
pub use multi_step_air::{
    ALLOW_PREDICATE, MultiStepDerivationAir, MultiStepStarkAir, MultiStepWitness,
    prove_authorization_stark, verify_authorization_stark,
};
pub use non_membership::{
    AugmentedDerivation, DerivationNonMembershipCheck, NonMembershipCheck, NonMembershipProof,
    NonMembershipProver, SetIdentifier, compute_set_accumulator, derive_alpha_for_set,
    verify_augmented_derivation, verify_non_membership_proof,
};
pub use non_revocation_air::{
    NonMembershipWitness, NonRevocationAir, NonRevocationWitness, SENTINEL_MAX, SENTINEL_MIN,
    SortedRevocationTree, prove_non_revocation, revocation_hash_to_field, verify_non_revocation,
};
pub use note_spending_air::{
    NoteSpendingAir, NoteSpendingWitness, prove_note_spend, verify_note_spend,
};
pub use predicate_air::{
    PredicateAir, PredicateProof, PredicateType, PredicateWitness, compute_blinded_fact_commitment,
    compute_fact_commitment, prove_in_range, prove_predicate, verify_in_range, verify_predicate,
};
pub use presentation::{
    AuthorizationProof, PresentationAir, PresentationProof, PresentationVerification,
    PresentationWitness, RealPresentationProof, prove_authorization,
};
pub use relational_predicate_air::{
    RelationType, RelationalPredicateAir, RelationalPredicateProof, RelationalPredicateWitness,
    compute_value_commitment, prove_relational, prove_value_comparison, verify_relational,
};
pub use sovereign_transition_air::{
    SOVEREIGN_PUBLIC_INPUTS, SOVEREIGN_TRANSITION_WIDTH, SovereignTransitionAir,
    bytes32_to_babybear, compute_cell_id_hash, compute_transfer_effects_hash,
    generate_sovereign_transition_trace,
};
pub use turn_validity_air::{
    TurnValidityAir, TurnValidityWitness, prove_turn_validity, verify_turn_validity,
};

// Schnorr signature scheme over BabyBear^8 elliptic curve.
pub use babybear8::BabyBear8;
pub use schnorr_curve::{CurvePoint, GENERATOR as SCHNORR_GENERATOR};
pub use schnorr_sig::{
    SchnorrPublicKey, SchnorrSecretKey, SchnorrSignature, compress_public_key, schnorr_keygen,
    schnorr_sign, schnorr_verify,
};

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
//! - `mock` (default): Uses a constraint satisfaction checker (mock prover)
//!   that evaluates AIR constraints directly without generating real STARK proofs.
//!   This validates circuit correctness and is suitable for development/testing.
//!
//! - `plonky3` (optional): Plonky3 dependencies available for future optimized prover.
//!
//! # Proof Backends
//!
//! - [`stark`]: Real STARK proof generation with FRI-based polynomial commitment.
//!   Produces actual cryptographic proofs (~24 KiB for a 4-level Merkle membership).
//!   Uses BLAKE3 Merkle trees, Fiat-Shamir transform, and Reed-Solomon encoding.
//! - [`mock_prover`]: Constraint satisfaction checker (validates circuit logic without
//!   generating real proofs, for development/testing).
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
//! - [`mock_prover`]: Constraint evaluator for testing.
//! - [`stark`]: Real STARK prover/verifier (FRI + Merkle + Fiat-Shamir).

pub mod body_membership;
pub mod derivation_air;
pub mod field;
pub mod fold_air;
pub mod ivc;
pub mod merkle_air;
pub mod mock_prover;
pub mod multi_step_air;
pub mod poseidon2;
pub mod poseidon2_air;
pub mod presentation;

pub mod note_spending_air;
pub mod stark;

#[cfg(feature = "plonky3")]
pub mod plonky3_prover;

#[cfg(feature = "plonky3")]
pub mod plonky3_recursion;

#[cfg(feature = "plonky3")]
pub mod plonky3_verifier_air;

pub mod backends;

#[cfg(test)]
mod tests;

// Re-export primary types.
pub use body_membership::{
    BodyFactMerkleProof, BodyMembershipProof, MembershipEntry,
    collect_body_fact_hashes, prove_authorization_with_membership,
    verify_authorization_with_membership,
};
pub use field::BabyBear;
pub use ivc::{
    FoldDelta, IvcBuilder, IvcPresentationProof, IvcProof, IvcVerification,
    StateTransitionAir, prove_ivc, prove_ivc_stark, verify_ivc, verify_ivc_stark,
};
pub use mock_prover::{Air, MockProof, MockProofResult, MockProver};
pub use multi_step_air::{
    ALLOW_PREDICATE, MultiStepDerivationAir, MultiStepStarkAir, MultiStepWitness,
    prove_authorization_stark, verify_authorization_stark,
};
pub use note_spending_air::{
    NoteSpendingAir, NoteSpendingWitness, prove_note_spend, verify_note_spend,
};
pub use presentation::{
    AuthorizationProof, PresentationAir, PresentationProof, PresentationVerification,
    PresentationWitness, RealPresentationProof, prove_authorization,
};

//! `pyana-bridge`: Connects plaintext token crates to the ZK proof system.
//!
//! This crate bridges two worlds:
//! - **Plaintext tokens** (`token`, `macaroon`): MacaroonToken/BiscuitToken with HMAC
//!   verification, caveat-based authorization, and attenuation.
//! - **ZK proof system** (`pyana-commit`, `pyana-trace`, `pyana-circuit`): Merkle-committed
//!   fact sets, Datalog derivation traces, and STARK-based presentation proofs.
//!
//! The bridge performs four key transformations:
//! 1. **Token to FactSet**: Converts macaroon caveats into committed facts.
//! 2. **Attenuation to FoldDelta**: Maps plaintext attenuation steps to ZK fold deltas.
//! 3. **Request to AuthorizationTrace**: Evaluates authorization against committed state.
//! 4. **Full Presentation**: Assembles a ZK-ready proof from a token chain.
//!
//! # Architecture
//!
//! ```text
//! MacaroonToken                          PresentationProof
//!    │                                         ▲
//!    │ convert                                  │ prove
//!    ▼                                         │
//! FactSet + SymbolTable ──────────────────► PresentationBuilder
//!    │                                         ▲
//!    │ attenuate                                │ add_step
//!    ▼                                         │
//! FoldDelta ─────────────────────────────────┘
//!    │
//!    │ authorize
//!    ▼
//! AuthorizationTrace
//! ```

pub mod authorize;
pub mod convert;
pub mod delta;
pub mod midnight;
pub mod midnight_observer;
pub mod present;

#[cfg(feature = "turn")]
pub mod verifier;

#[cfg(test)]
mod tests;

// Re-export primary types for convenience.
pub use authorize::{AuthError, authorize_with_trace};
pub use convert::{grant_to_facts, macaroon_to_factset};
pub use delta::attenuation_to_delta;
pub use present::{
    BridgeCommittedThresholdProof, BridgePredicateProof, BridgePredicateProofInner,
    BridgePresentationBuilder, BridgePresentationProof, DEFAULT_MAX_PROOF_AGE_SECS,
    FederationRegistry, Predicate, ProgramProveError, UnsafeLocalOnlyMarker, VerifiedPresentation,
    VerifierConfig, VerifyError, WirePresentationProof, bb_from_bytes, bb_to_bytes,
    compute_revealed_facts_commitment, prove_committed_threshold, prove_predicate_for_fact,
    prove_predicate_program, prove_predicate_program_full, verify_committed_threshold_proof,
    verify_fold_chain, verify_predicate_program, verify_predicate_proof,
    verify_presentation_complete, verify_presentation_full, verify_proof_complete,
    verify_revealed_facts_commitment, verify_wire_fold_chain,
};
#[cfg(feature = "turn")]
pub use verifier::{DslAwareProofVerifier, StarkProofVerifier};

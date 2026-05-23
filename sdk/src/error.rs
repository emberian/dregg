//! Error types for the pyana SDK.

use pyana_bridge::AuthError;
use pyana_token::TokenError;
use pyana_turn::TurnError;

/// Unified error type for SDK operations.
#[derive(Debug, thiserror::Error)]
pub enum SdkError {
    /// A token operation failed (minting, attenuation, verification).
    #[error("token error: {0}")]
    Token(#[from] TokenError),

    /// A turn execution failed (precondition, authorization, budget).
    #[error("turn error: {0}")]
    Turn(#[from] TurnError),

    /// Authorization or proof generation failed.
    #[error("auth/proof error: {0}")]
    Auth(#[from] AuthError),

    /// A wire protocol operation failed.
    #[error("wire error: {0}")]
    Wire(String),

    /// The wallet has no token matching the requested operation.
    #[error("no such token: {0}")]
    TokenNotFound(String),

    /// The wallet does not have the required key material.
    #[error("missing key material: {0}")]
    MissingKey(String),

    /// A delegation or attenuation was invalid.
    #[error("invalid delegation: {0}")]
    InvalidDelegation(String),

    /// A duplicate receipt was detected (same turn_hash already in chain).
    #[error("duplicate receipt: turn_hash already exists in receipt chain")]
    DuplicateReceipt {
        /// The turn_hash of the duplicate receipt.
        turn_hash: [u8; 32],
    },

    /// Attenuation does not narrow the original token's permissions.
    #[error("attenuation does not narrow: {0}")]
    AttenuationNotNarrowing(String),

    /// The remote silo rejected the operation.
    #[error("silo rejected: {0}")]
    Rejected(String),

    /// The response digest does not match the expected request digest (MITM detected).
    #[error("digest mismatch: response bound to different request than sent")]
    DigestMismatch,

    /// The federation root from the remote silo does not match the expected pinned root.
    #[error("federation root mismatch: remote root does not match pinned value")]
    FederationRootMismatch,

    /// A non-membership proof failed cryptographic verification.
    #[error("non-membership proof verification failed: {0}")]
    NonMembershipVerificationFailed(String),

    /// A witness construction failed (e.g., unground variable in predicate proof).
    #[error("invalid witness: {0}")]
    InvalidWitness(String),
}

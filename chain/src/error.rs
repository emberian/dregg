//! Error types for the chain crate.

use thiserror::Error;

/// Errors that can occur during EVM proof wrapping and verification.
#[derive(Debug, Error)]
pub enum ChainError {
    /// The STARK proof bytes could not be deserialized.
    #[error("invalid STARK proof: {0}")]
    InvalidProof(String),

    /// SP1 proving failed.
    #[error("SP1 proving failed: {0}")]
    ProvingFailed(String),

    /// SP1 toolchain is not installed.
    #[error("SP1 toolchain not installed. Run: curl -L https://sp1.succinct.xyz | bash && sp1up")]
    ToolchainMissing,

    /// The guest program ELF has not been built.
    #[error("guest program not built. Run: cd chain/program && cargo prove build")]
    GuestNotBuilt,

    /// On-chain verification call failed.
    #[error("on-chain verification failed: {0}")]
    OnChainError(String),

    /// RPC connection error.
    #[error("RPC error: {0}")]
    RpcError(String),

    /// The proof was rejected by the on-chain verifier.
    #[error("proof rejected by on-chain verifier")]
    ProofRejected,

    /// Generic error.
    #[error(transparent)]
    Other(#[from] anyhow::Error),
}

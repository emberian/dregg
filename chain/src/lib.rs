//! # pyana-chain: EVM On-Chain Verification via SP1
//!
//! This crate wraps pyana STARK proofs in SP1's zkVM to produce Groth16 proofs
//! that are cheaply verifiable on Ethereum/Base (~200k gas).
//!
//! ## Architecture
//!
//! ```text
//! pyana STARK proof (large, not EVM-friendly)
//!        |
//!        v
//! SP1 Guest Program (verifies STARK inside RISC-V zkVM)
//!        |
//!        v
//! SP1 Groth16 proof (compact, ~200k gas on EVM)
//!        |
//!        v
//! SP1 Verifier Contract on Base/Ethereum
//! ```
//!
//! ## Setup Requirements
//!
//! SP1 requires its custom toolchain for building guest programs:
//!
//! ```bash
//! # Install SP1 toolchain
//! curl -L https://sp1.succinct.xyz | bash
//! sp1up
//!
//! # Build the guest program (produces ELF binary)
//! cd chain/program && cargo prove build
//! ```
//!
//! ## Usage
//!
//! ```rust,no_run
//! use pyana_chain::{wrap_for_evm, verify_on_chain, EvmProof};
//!
//! # async fn example() -> anyhow::Result<()> {
//! // Generate a STARK proof with the circuit crate, then wrap it:
//! let stark_proof_bytes: Vec<u8> = vec![]; // from circuit::stark::proof_to_bytes()
//! let public_inputs: Vec<u32> = vec![12345, 67890]; // leaf hash + root
//!
//! let evm_proof = wrap_for_evm(&stark_proof_bytes, &public_inputs).await?;
//!
//! // Submit to Base for on-chain verification:
//! let verified = verify_on_chain(
//!     &evm_proof,
//!     "https://mainnet.base.org",
//!     &evm_proof.verifier_address,
//! ).await?;
//! assert!(verified);
//! # Ok(())
//! # }
//! ```
//!
//! ## SP1 Verifier Contracts (deployed by Succinct)
//!
//! SP1's Groth16 verifier is deployed at deterministic addresses:
//! - **Ethereum Mainnet**: See <https://docs.succinct.xyz/docs/sp1/verification/onchain/contract-addresses>
//! - **Base Mainnet**: Same address via CREATE2 deterministic deployment
//! - **Base Sepolia**: Available for testing
//!
//! The verifier contract interface:
//! ```solidity
//! interface ISP1Verifier {
//!     function verifyProof(
//!         bytes32 programVKey,
//!         bytes calldata publicValues,
//!         bytes calldata proofBytes
//!     ) external view;
//! }
//! ```

pub mod error;
pub mod prove;
pub mod verify;

#[cfg(feature = "mock")]
pub mod mock;

pub use error::ChainError;
pub use prove::{wrap_for_evm, EvmProof};
pub use verify::verify_on_chain;

/// The SP1 program verification key (vkey).
/// This is computed from the guest program ELF and identifies what program was proven.
/// On-chain, the verifier checks `proof.vkey == expected_vkey` to ensure the correct
/// program (our STARK verifier) was executed.
///
/// This will be populated at build time once the guest program is compiled with `cargo prove build`.
/// For now it's a placeholder that the build script will fill in.
pub const SP1_PROGRAM_VKEY: &str = "PLACEHOLDER_VKEY_BUILD_WITH_SP1_TOOLCHAIN";

/// Known SP1 verifier contract addresses (Succinct deployments via CREATE2).
/// These are the ISP1Verifier gateway contracts.
/// See: https://docs.succinct.xyz/docs/sp1/verification/onchain/contract-addresses
pub mod contracts {
    /// SP1 Verifier Gateway on Ethereum Mainnet
    pub const ETHEREUM_MAINNET: &str = "0x3B6041173B80E77f038f3F2C0f9744f04837185e";
    /// SP1 Verifier Gateway on Base Mainnet
    pub const BASE_MAINNET: &str = "0x3B6041173B80E77f038f3F2C0f9744f04837185e";
    /// SP1 Verifier Gateway on Base Sepolia (testnet)
    pub const BASE_SEPOLIA: &str = "0x3B6041173B80E77f038f3F2C0f9744f04837185e";
}

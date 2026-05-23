//! # pyana-stablecoin
//!
//! A collateralized stablecoin (CDP) application built on Pyana's sovereign cell model.
//!
//! Users lock collateral assets in escrow and mint stablecoins (PUSD) against them.
//! The system enforces over-collateralization via STARK proofs: every mint/repay action
//! must carry a proof that `collateral_value * 10000 >= debt * ratio_bps`.
//!
//! # Architecture
//!
//! ```text
//! +──────────────+     +───────────────+     +──────────────+
//! |   CDP Owner  |────>| CDP Cell      |<────| Liquidator   |
//! | (deposits)   |     | (circuit prog)|     | (seizes)     |
//! +──────────────+     +───────────────+     +──────────────+
//!        |                    |                     |
//!   Deposit collateral   STARK-enforced       Liquidation
//!   + mint PUSD         ratio constraint      when ratio < 150%
//!        |                    |                     |
//!        v                    v                     v
//! +──────────────+     +───────────────+     +──────────────+
//! | Escrow       |     | Price Oracle  |     | Note Tree    |
//! | (collateral) |     | (attestation) |     | (PUSD notes) |
//! +──────────────+     +───────────────+     +──────────────+
//! ```
//!
//! # Components
//!
//! - [`cdp`]: Collateral position lifecycle (open, mint, repay, close)
//! - [`oracle`]: Price attestation with freshness checks and commitment binding
//! - [`circuit`]: CDP circuit descriptor (STARK-verifiable collateral ratio)
//! - [`liquidation`]: Liquidation engine (monitoring and execution)
//!
//! # Pyana Primitives Used
//!
//! - `CellProgram::Circuit` via `CircuitDescriptor` for the CDP enforcement circuit
//! - `ProgramRegistry` for deploying and verifying the CDP program
//! - `Note` with `PUSD_ASSET_TYPE` for stablecoin notes
//! - `EscrowCondition::ProofPresented` for collateral locking
//! - Poseidon2 hashing for oracle commitment binding
//! - STARK proofs (BabyBear field, FRI) for every state transition

pub mod cdp;
pub mod circuit;
pub mod liquidation;
pub mod oracle;
pub mod server;

#[cfg(test)]
mod tests;

// Re-exports for convenience.
pub use cdp::{
    CdpError, CdpTransition, CollateralPosition, ETH_ASSET_TYPE, PUSD_ASSET_TYPE, PositionStatus,
    StablecoinRegistry,
};
pub use circuit::{
    BPS_SCALE, CDP_PUBLIC_INPUTS, CDP_TRACE_WIDTH, CdpWitness, MIN_RATIO_BPS, cdp_cell_program,
    cdp_circuit_descriptor, deploy_cdp_program, prove_cdp_ratio, verify_cdp_ratio,
};
pub use liquidation::{
    DEFAULT_LIQUIDATION_BONUS_BPS, LiquidationEngine, LiquidationError, LiquidationResult,
};
pub use oracle::{
    OracleError, PriceAttestation, PriceOracle, test_attestation, test_attestation_signed,
    test_attestation_unsigned, test_oracle_pubkey,
};

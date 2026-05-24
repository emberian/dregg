//! Computron Economics: minting, supply management, and equilibrium.
//!
//! The system charges computron fees on every turn (50% proposer, 30% treasury, 20% burn).
//! Without minting, the supply is purely deflationary and eventually deadlocks.
//!
//! This module provides epoch-based minting to the treasury, with a disinflationary
//! schedule that converges toward a target supply equilibrium.
//!
//! # Design
//!
//! - **Epoch**: every `epoch_length` blocks (default 1000).
//! - **Issuance**: geometrically decreasing per epoch (halving every `halving_interval` epochs).
//! - **Cap**: total lifetime supply is bounded by `max_supply`.
//! - **Treasury**: newly minted computrons go to the federation treasury cell, which
//!   distributes them via governance (staking rewards, grants, fee subsidies).
//! - **Equilibrium target**: when burn rate matches issuance rate, the supply stabilizes.
//!   The halving schedule ensures this convergence regardless of transaction volume.
//!
//! # Integration
//!
//! The executor calls [`EpochMinter::maybe_mint`] at each block height. If the block
//! crosses an epoch boundary, the minter issues computrons to the treasury cell.
//! The minter is stateless between restarts (derives state from `current_height` alone).

use pyana_cell::{CellId, Ledger};
use serde::{Deserialize, Serialize};

// ─── Minting Policy ───────────────────────────────────────────────────────────

/// Configuration for epoch-based computron minting.
///
/// This is the monetary policy of the federation. Changes to these parameters
/// require a constitutional amendment (supermajority vote).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MintingPolicy {
    /// Number of blocks per epoch. Minting occurs once per epoch.
    /// Default: 1000 blocks.
    pub epoch_length: u64,

    /// Base issuance for the first epoch (in computrons).
    /// Each subsequent epoch issues `base_issuance >> (epoch / halving_interval)`.
    /// Default: 1_000_000 computrons per epoch.
    pub base_issuance: u64,

    /// Number of epochs between each halving of the issuance rate.
    /// Default: 100 epochs (100,000 blocks at epoch_length=1000).
    pub halving_interval: u64,

    /// Maximum total supply (hard cap). Once cumulative issuance reaches this,
    /// no more computrons are minted regardless of epoch.
    /// Default: 1_000_000_000 (1 billion).
    pub max_supply: u64,

    /// The treasury cell that receives minted computrons.
    /// This cell distributes via governance mechanisms (staking, grants, subsidies).
    pub treasury_cell: CellId,

    /// Total computrons minted so far (across all epochs since genesis).
    /// Persisted as part of federation state.
    pub total_minted: u64,

    /// The last epoch at which minting occurred.
    /// Used to detect epoch boundaries efficiently.
    pub last_minted_epoch: u64,
}

impl MintingPolicy {
    /// Create a new minting policy with default parameters.
    ///
    /// # Arguments
    ///
    /// * `treasury_cell` - The cell that receives newly minted computrons.
    pub fn new(treasury_cell: CellId) -> Self {
        Self {
            epoch_length: 1000,
            base_issuance: 1_000_000,
            halving_interval: 100,
            max_supply: 1_000_000_000,
            treasury_cell,
            total_minted: 0,
            last_minted_epoch: 0,
        }
    }

    /// Create a minting policy with custom parameters.
    pub fn custom(
        treasury_cell: CellId,
        epoch_length: u64,
        base_issuance: u64,
        halving_interval: u64,
        max_supply: u64,
    ) -> Self {
        Self {
            epoch_length,
            base_issuance,
            halving_interval,
            max_supply,
            treasury_cell,
            total_minted: 0,
            last_minted_epoch: 0,
        }
    }

    /// Compute which epoch a given block height falls in.
    pub fn epoch_for_height(&self, height: u64) -> u64 {
        if self.epoch_length == 0 {
            return 0;
        }
        height / self.epoch_length
    }

    /// Compute the issuance for a given epoch number.
    ///
    /// Applies geometric halving: `base_issuance >> (epoch / halving_interval)`.
    /// Returns 0 if the halving has reduced issuance below 1 or if max_supply
    /// would be exceeded.
    pub fn issuance_for_epoch(&self, epoch: u64) -> u64 {
        if self.halving_interval == 0 {
            return 0;
        }
        let halvings = epoch / self.halving_interval;
        // After 64 halvings, issuance is effectively zero (u64 shift saturates).
        if halvings >= 64 {
            return 0;
        }
        let issuance = self.base_issuance >> halvings;
        // Clamp to remaining supply headroom.
        let remaining = self.max_supply.saturating_sub(self.total_minted);
        issuance.min(remaining)
    }

    /// Check whether minting should occur at the given height and return the amount.
    ///
    /// Returns `Some(amount)` if this height crosses an epoch boundary that hasn't
    /// been minted yet, and the amount is > 0. Returns `None` otherwise.
    pub fn should_mint(&self, height: u64) -> Option<u64> {
        if self.epoch_length == 0 {
            return None;
        }
        let epoch = self.epoch_for_height(height);
        // Only mint at epoch boundaries (first block of new epoch).
        if height % self.epoch_length != 0 {
            return None;
        }
        // Don't re-mint for an epoch we've already processed.
        if epoch <= self.last_minted_epoch && self.total_minted > 0 {
            return None;
        }
        let amount = self.issuance_for_epoch(epoch);
        if amount > 0 { Some(amount) } else { None }
    }
}

// ─── Epoch Minter ─────────────────────────────────────────────────────────────

/// Epoch-based minter that integrates with the executor's block processing.
///
/// Called once per block by the executor. When an epoch boundary is crossed,
/// credits the treasury cell with the epoch's issuance.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct EpochMinter {
    /// The minting policy configuration.
    pub policy: MintingPolicy,
}

/// Result of a minting operation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MintResult {
    /// The epoch at which minting occurred.
    pub epoch: u64,
    /// The amount minted.
    pub amount: u64,
    /// The recipient cell.
    pub treasury_cell: CellId,
    /// New cumulative total minted.
    pub total_minted: u64,
}

impl EpochMinter {
    /// Create a new epoch minter with the given policy.
    pub fn new(policy: MintingPolicy) -> Self {
        Self { policy }
    }

    /// Create an epoch minter with default parameters for the given treasury cell.
    pub fn with_treasury(treasury_cell: CellId) -> Self {
        Self {
            policy: MintingPolicy::new(treasury_cell),
        }
    }

    /// Check and apply minting for the given block height.
    ///
    /// If this height crosses an epoch boundary:
    /// 1. Computes the epoch issuance (halving schedule applied).
    /// 2. Credits the treasury cell's balance in the ledger.
    /// 3. Updates the policy's cumulative state.
    ///
    /// Returns `Some(MintResult)` if minting occurred, `None` otherwise.
    ///
    /// # Arguments
    ///
    /// * `ledger` - The mutable ledger to credit the treasury cell.
    /// * `height` - The current block height being processed.
    pub fn maybe_mint(&mut self, ledger: &mut Ledger, height: u64) -> Option<MintResult> {
        let amount = self.policy.should_mint(height)?;
        let epoch = self.policy.epoch_for_height(height);

        // Credit the treasury cell. If it doesn't exist in the ledger,
        // the minted computrons are effectively lost (misconfiguration).
        // Production deployments MUST ensure the treasury cell exists at genesis.
        if let Some(treasury) = ledger.get_mut(&self.policy.treasury_cell) {
            treasury.state.set_balance(treasury.state.balance().saturating_add(amount));
        } else {
            // Treasury cell not found — this is a configuration error.
            // Log and skip rather than panic. The computrons are not created.
            // In production, this should trigger an alert.
            return None;
        }

        // Update policy state.
        self.policy.total_minted = self.policy.total_minted.saturating_add(amount);
        self.policy.last_minted_epoch = epoch;

        Some(MintResult {
            epoch,
            amount,
            treasury_cell: self.policy.treasury_cell,
            total_minted: self.policy.total_minted,
        })
    }

    /// Get the current total minted computrons.
    pub fn total_minted(&self) -> u64 {
        self.policy.total_minted
    }

    /// Get the remaining supply headroom before hitting max_supply.
    pub fn remaining_supply(&self) -> u64 {
        self.policy
            .max_supply
            .saturating_sub(self.policy.total_minted)
    }

    /// Estimate the annual issuance rate given a block time in seconds.
    ///
    /// Useful for economic modeling and governance dashboards.
    pub fn estimated_annual_issuance(&self, block_time_secs: u64) -> u64 {
        if block_time_secs == 0 || self.policy.epoch_length == 0 {
            return 0;
        }
        let blocks_per_year = 365 * 24 * 3600 / block_time_secs;
        let epochs_per_year = blocks_per_year / self.policy.epoch_length;
        let current_epoch = self.policy.last_minted_epoch;

        let mut total = 0u64;
        for i in 0..epochs_per_year {
            total = total.saturating_add(self.policy.issuance_for_epoch(current_epoch + i));
        }
        total
    }

    /// Compute the equilibrium supply level for a given burn rate.
    ///
    /// At equilibrium, annual issuance == annual burn. This returns the epoch
    /// number at which issuance per epoch drops below the given burn per epoch.
    /// After this epoch, the supply is stable (burn >= issuance).
    pub fn equilibrium_epoch(&self, burn_per_epoch: u64) -> Option<u64> {
        if self.policy.halving_interval == 0 || burn_per_epoch == 0 {
            return None;
        }
        // Find the epoch where issuance_for_epoch(e) <= burn_per_epoch.
        // Since issuance halves every halving_interval epochs, this is:
        // base_issuance >> (e / halving_interval) <= burn_per_epoch
        // => e / halving_interval >= log2(base_issuance / burn_per_epoch)
        if self.policy.base_issuance <= burn_per_epoch {
            return Some(0); // Already at or below equilibrium from epoch 0.
        }
        let ratio = self.policy.base_issuance / burn_per_epoch;
        // ceil(log2(ratio)): number of halvings until issuance <= burn rate.
        let halvings_needed = (u64::BITS - (ratio - 1).leading_zeros()) as u64;
        Some(halvings_needed * self.policy.halving_interval)
    }
}

// ─── Tests ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_cell::CellId;

    fn test_treasury_cell() -> CellId {
        CellId::derive_raw(&[0xAA; 32], &[0xBB; 32])
    }

    #[test]
    fn epoch_calculation() {
        let policy = MintingPolicy::new(test_treasury_cell());
        assert_eq!(policy.epoch_for_height(0), 0);
        assert_eq!(policy.epoch_for_height(999), 0);
        assert_eq!(policy.epoch_for_height(1000), 1);
        assert_eq!(policy.epoch_for_height(1001), 1);
        assert_eq!(policy.epoch_for_height(5000), 5);
    }

    #[test]
    fn issuance_halving() {
        let policy = MintingPolicy::new(test_treasury_cell());
        // Epoch 0-99: base_issuance = 1_000_000
        assert_eq!(policy.issuance_for_epoch(0), 1_000_000);
        assert_eq!(policy.issuance_for_epoch(50), 1_000_000);
        assert_eq!(policy.issuance_for_epoch(99), 1_000_000);
        // Epoch 100-199: halved to 500_000
        assert_eq!(policy.issuance_for_epoch(100), 500_000);
        assert_eq!(policy.issuance_for_epoch(199), 500_000);
        // Epoch 200-299: halved again to 250_000
        assert_eq!(policy.issuance_for_epoch(200), 250_000);
        // Very late epoch: effectively zero
        assert_eq!(policy.issuance_for_epoch(6400), 0);
    }

    #[test]
    fn max_supply_cap() {
        let mut policy = MintingPolicy::new(test_treasury_cell());
        policy.max_supply = 1_500_000;
        policy.total_minted = 1_400_000;
        // Only 100_000 remaining, even though epoch 0 would issue 1_000_000
        assert_eq!(policy.issuance_for_epoch(0), 100_000);
    }

    #[test]
    fn should_mint_at_epoch_boundary() {
        let policy = MintingPolicy::new(test_treasury_cell());
        // Not an epoch boundary
        assert_eq!(policy.should_mint(1), None);
        assert_eq!(policy.should_mint(500), None);
        assert_eq!(policy.should_mint(999), None);
        // Epoch boundary at height 0 (genesis)
        assert_eq!(policy.should_mint(0), Some(1_000_000));
        // Epoch boundary at height 1000
        assert_eq!(policy.should_mint(1000), Some(1_000_000));
    }

    #[test]
    fn should_mint_no_double_mint() {
        let mut policy = MintingPolicy::new(test_treasury_cell());
        // Simulate that epoch 1 was already minted.
        policy.last_minted_epoch = 1;
        policy.total_minted = 1_000_000;
        // Height 1000 = epoch 1, already minted
        assert_eq!(policy.should_mint(1000), None);
        // Height 2000 = epoch 2, not yet minted
        assert_eq!(policy.should_mint(2000), Some(1_000_000));
    }

    #[test]
    fn minter_integration_with_ledger() {
        let treasury_id = test_treasury_cell();
        let mut ledger = Ledger::new();
        // Create treasury cell with initial balance
        let treasury = pyana_cell::Cell::with_balance([0xAA; 32], [0xBB; 32], 1000);
        ledger.insert_cell(treasury).unwrap();

        let mut minter = EpochMinter::with_treasury(treasury_id);

        // Block 0: epoch boundary, should mint
        let result = minter.maybe_mint(&mut ledger, 0);
        assert!(result.is_some());
        let r = result.unwrap();
        assert_eq!(r.amount, 1_000_000);
        assert_eq!(r.epoch, 0);
        assert_eq!(minter.total_minted(), 1_000_000);

        // Check treasury balance
        let treasury_cell = ledger.get(&treasury_id).unwrap();
        assert_eq!(treasury_cell.state.balance(), 1000 + 1_000_000);

        // Block 500: not an epoch boundary, should not mint
        let result = minter.maybe_mint(&mut ledger, 500);
        assert!(result.is_none());

        // Block 1000: next epoch boundary, should mint
        let result = minter.maybe_mint(&mut ledger, 1000);
        assert!(result.is_some());
        let r = result.unwrap();
        assert_eq!(r.amount, 1_000_000);
        assert_eq!(r.epoch, 1);
        assert_eq!(minter.total_minted(), 2_000_000);
    }

    #[test]
    fn minter_missing_treasury_returns_none() {
        let treasury_id = test_treasury_cell();
        let mut ledger = Ledger::new();
        // Treasury cell NOT in ledger

        let mut minter = EpochMinter::with_treasury(treasury_id);
        let result = minter.maybe_mint(&mut ledger, 0);
        // Should return None (treasury cell not found)
        assert!(result.is_none());
        // total_minted should NOT increase
        assert_eq!(minter.total_minted(), 0);
    }

    #[test]
    fn minter_max_supply_stops_minting() {
        let treasury_id = test_treasury_cell();
        let mut ledger = Ledger::new();
        let treasury = pyana_cell::Cell::with_balance([0xAA; 32], [0xBB; 32], 0);
        ledger.insert_cell(treasury).unwrap();

        let mut minter = EpochMinter::new(MintingPolicy::custom(
            treasury_id,
            10,   // epoch_length
            500,  // base_issuance
            100,  // halving_interval
            1000, // max_supply = 1000
        ));

        // Epoch 0 (height 0): mint 500
        let r = minter.maybe_mint(&mut ledger, 0).unwrap();
        assert_eq!(r.amount, 500);
        assert_eq!(minter.total_minted(), 500);

        // Epoch 1 (height 10): mint 500 (exactly reaches max)
        let r = minter.maybe_mint(&mut ledger, 10).unwrap();
        assert_eq!(r.amount, 500);
        assert_eq!(minter.total_minted(), 1000);

        // Epoch 2 (height 20): cannot mint (max_supply reached)
        let result = minter.maybe_mint(&mut ledger, 20);
        assert!(result.is_none());
    }

    #[test]
    fn equilibrium_epoch_calculation() {
        let minter = EpochMinter::with_treasury(test_treasury_cell());
        // If burn rate is 1_000_000 per epoch, we're at equilibrium from epoch 0
        assert_eq!(minter.equilibrium_epoch(1_000_000), Some(0));
        // If burn rate is 500_000, we need 1 halving (100 epochs)
        assert_eq!(minter.equilibrium_epoch(500_000), Some(100));
        // If burn rate is 250_000, we need 2 halvings (200 epochs)
        assert_eq!(minter.equilibrium_epoch(250_000), Some(200));
    }

    #[test]
    fn zero_epoch_length_does_not_panic() {
        let mut policy = MintingPolicy::new(test_treasury_cell());
        policy.epoch_length = 0;
        assert_eq!(policy.epoch_for_height(100), 0);
        assert_eq!(policy.should_mint(100), None);
    }
}

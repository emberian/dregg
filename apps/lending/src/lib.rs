//! Decentralized lending/borrowing protocol built on pyana primitives.
//!
//! # Architecture
//!
//! ```text
//! ┌──────────────┐     ┌──────────────────┐     ┌──────────────┐
//! │   Supplier   │────▶│   LendingPool    │◀────│   Borrower   │
//! │  (deposits)  │     │  (market state)  │     │  (borrows)   │
//! └──────────────┘     └──────────────────┘     └──────────────┘
//!                              │    ▲
//!                              │    │
//!                              ▼    │
//!                      ┌──────────────────┐
//!                      │   Liquidator     │
//!                      │  (health check)  │
//!                      └──────────────────┘
//! ```
//!
//! # Pyana Primitives Used
//!
//! - **ProofObligation**: Borrower's debt obligation — stake is collateral,
//!   slashed on undercollateralization.
//! - **TemporalPredicate**: Interest accrual proof — value grows by rate each block.
//! - **ConditionalTurn**: Liquidation — conditional on health factor < 1.0.
//! - **Note**: Supply tokens, borrow tokens, interest-bearing receipt tokens.
//! - **Circuit (AIR)**: HealthFactorAir and InterestAccrualAir enforce protocol rules.
//!
//! # Lifecycle
//!
//! 1. Supplier deposits tokens → receives SupplyReceipt
//! 2. Borrower deposits collateral + borrows against it → BorrowPosition created
//! 3. Interest accrues per-block based on utilization
//! 4. Borrower repays → collateral unlocked
//! 5. If health factor < 1.0 → liquidator repays debt, seizes collateral + bonus

pub mod borrow;
pub mod circuit;
pub mod executor;
pub mod interest;
pub mod liquidation;
pub mod server;
pub mod supply;
pub mod warnings;

#[cfg(test)]
mod tests;

use pyana_types::CellId;
use serde::{Deserialize, Serialize};

use borrow::{BorrowPosition, CollateralEntry, DEFAULT_LIQUIDATION_THRESHOLD_BPS};
use interest::{BLOCKS_PER_YEAR, INDEX_PRECISION, InterestRateModel, compute_new_borrow_index};
use liquidation::{LiquidationEngine, LiquidationResult};
use supply::{SupplyPosition, SupplyReceipt};

// =============================================================================
// Core Types
// =============================================================================

/// A lending market for a single asset type.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Market {
    /// Asset type identifier for this market.
    pub asset_id: u64,
    /// Total amount supplied (deposited) into the market.
    pub total_supply: u64,
    /// Total amount currently borrowed from the market.
    pub total_borrows: u64,
    /// Total reserves (protocol fees).
    pub total_reserves: u64,
    /// Current borrow index (tracks cumulative interest, scaled by INDEX_PRECISION).
    pub borrow_index: u128,
    /// Last block at which interest was accrued globally.
    pub last_accrual_block: u64,
    /// Interest rate model for this market.
    pub rate_model: InterestRateModel,
    /// Liquidation threshold for this market (bps).
    pub liquidation_threshold_bps: u64,
    /// Reserve factor: fraction of interest that goes to reserves (bps).
    pub reserve_factor_bps: u64,
    /// Whether this market is active (accepting deposits/borrows).
    pub active: bool,
}

impl Market {
    /// Create a new market with default parameters.
    pub fn new(asset_id: u64) -> Self {
        Self {
            asset_id,
            total_supply: 0,
            total_borrows: 0,
            total_reserves: 0,
            borrow_index: INDEX_PRECISION,
            last_accrual_block: 0,
            rate_model: InterestRateModel::default(),
            liquidation_threshold_bps: DEFAULT_LIQUIDATION_THRESHOLD_BPS,
            reserve_factor_bps: 1_000, // 10% of interest goes to reserves
            active: true,
        }
    }

    /// Create a market with a custom rate model.
    pub fn with_rate_model(asset_id: u64, model: InterestRateModel) -> Self {
        Self {
            rate_model: model,
            ..Self::new(asset_id)
        }
    }

    /// Get the current utilization in basis points.
    pub fn utilization_bps(&self) -> u64 {
        self.rate_model
            .utilization_bps(self.total_supply, self.total_borrows)
    }

    /// Accrue interest globally for this market.
    ///
    /// Updates the borrow index, total borrows, and reserves.
    pub fn accrue_interest(&mut self, current_block: u64) {
        if current_block <= self.last_accrual_block {
            return;
        }
        let blocks_elapsed = current_block - self.last_accrual_block;
        let utilization = self.utilization_bps();
        let borrow_rate = self.rate_model.borrow_rate_bps(utilization);

        // Compute interest accrued on total borrows
        let interest_accrued = self.rate_model.accrue_interest(
            self.total_borrows,
            utilization,
            blocks_elapsed,
            BLOCKS_PER_YEAR,
        );

        // Update borrow index
        self.borrow_index = compute_new_borrow_index(
            self.borrow_index,
            borrow_rate,
            blocks_elapsed,
            BLOCKS_PER_YEAR,
        );

        // Protocol reserves
        let reserve_portion = (interest_accrued as u128 * self.reserve_factor_bps as u128
            / interest::BPS_SCALE as u128) as u64;
        self.total_reserves += reserve_portion;

        // Total borrows grows by interest
        self.total_borrows += interest_accrued;
        // Total supply also grows (interest is paid to suppliers)
        self.total_supply += interest_accrued - reserve_portion;

        self.last_accrual_block = current_block;
    }

    /// Get the current supply APY in basis points.
    pub fn supply_apy_bps(&self) -> u64 {
        self.rate_model.supply_rate_bps(self.utilization_bps())
    }

    /// Get the current borrow APY in basis points.
    pub fn borrow_apy_bps(&self) -> u64 {
        self.rate_model.borrow_rate_bps(self.utilization_bps())
    }
}

/// The lending pool: manages multiple markets and positions.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct LendingPool {
    /// Markets keyed by asset ID.
    pub markets: Vec<Market>,
    /// All supply positions.
    pub supply_positions: Vec<SupplyPosition>,
    /// All borrow positions.
    pub borrow_positions: Vec<BorrowPosition>,
    /// Liquidation engine configuration.
    #[serde(skip)]
    pub liquidation_engine: Option<LiquidationEngine>,
    /// Current block height.
    pub current_block: u64,
}

impl Default for LendingPool {
    fn default() -> Self {
        Self::new()
    }
}

impl LendingPool {
    /// Create a new empty lending pool.
    pub fn new() -> Self {
        Self {
            markets: Vec::new(),
            supply_positions: Vec::new(),
            borrow_positions: Vec::new(),
            liquidation_engine: Some(LiquidationEngine::default()),
            current_block: 0,
        }
    }

    /// Add a new market to the pool.
    pub fn add_market(&mut self, market: Market) {
        self.markets.push(market);
    }

    /// Get a market by asset ID.
    pub fn get_market(&self, asset_id: u64) -> Option<&Market> {
        self.markets.iter().find(|m| m.asset_id == asset_id)
    }

    /// Get a mutable market by asset ID.
    pub fn get_market_mut(&mut self, asset_id: u64) -> Option<&mut Market> {
        self.markets.iter_mut().find(|m| m.asset_id == asset_id)
    }

    /// Advance the pool to a new block height, accruing interest on all markets.
    pub fn advance_to_block(&mut self, block: u64) {
        self.current_block = block;
        for market in &mut self.markets {
            market.accrue_interest(block);
        }
    }

    /// Supply (deposit) tokens into a market.
    ///
    /// Returns a SupplyReceipt on success.
    pub fn supply(
        &mut self,
        supplier: CellId,
        asset_id: u64,
        amount: u64,
    ) -> Result<SupplyReceipt, LendingError> {
        let market = self
            .get_market_mut(asset_id)
            .ok_or(LendingError::MarketNotFound { asset_id })?;

        if !market.active {
            return Err(LendingError::MarketInactive { asset_id });
        }

        let borrow_index = market.borrow_index;
        market.total_supply += amount;

        let position =
            SupplyPosition::new(supplier, asset_id, amount, borrow_index, self.current_block);
        let receipt = SupplyReceipt::from_position(&position);
        self.supply_positions.push(position);

        Ok(receipt)
    }

    /// Withdraw a supply position.
    ///
    /// Returns the withdrawal amount on success.
    pub fn withdraw(&mut self, position_id: &[u8; 32]) -> Result<u64, LendingError> {
        // Find position index first
        let pos_idx = self
            .supply_positions
            .iter()
            .position(|p| &p.id == position_id)
            .ok_or(LendingError::PositionNotFound)?;

        if self.supply_positions[pos_idx].withdrawn {
            return Err(LendingError::AlreadyWithdrawn);
        }

        let asset_id = self.supply_positions[pos_idx].asset_id;
        let market = self
            .markets
            .iter()
            .find(|m| m.asset_id == asset_id)
            .ok_or(LendingError::MarketNotFound { asset_id })?;

        let amount = self.supply_positions[pos_idx].current_balance(market.borrow_index);
        self.supply_positions[pos_idx].withdrawn = true;

        // Update market totals
        let market = self
            .get_market_mut(asset_id)
            .ok_or(LendingError::MarketNotFound { asset_id })?;
        market.total_supply = market.total_supply.saturating_sub(amount);

        Ok(amount)
    }

    /// Borrow tokens against collateral.
    ///
    /// The borrower must have already deposited collateral.
    pub fn borrow(
        &mut self,
        borrower: CellId,
        borrow_asset_id: u64,
        amount: u64,
        collateral: Vec<CollateralEntry>,
    ) -> Result<[u8; 32], LendingError> {
        let market = self
            .get_market(borrow_asset_id)
            .ok_or(LendingError::MarketNotFound {
                asset_id: borrow_asset_id,
            })?;

        if !market.active {
            return Err(LendingError::MarketInactive {
                asset_id: borrow_asset_id,
            });
        }

        if amount > market.total_supply - market.total_borrows {
            return Err(LendingError::InsufficientLiquidity {
                available: market.total_supply - market.total_borrows,
                requested: amount,
            });
        }

        let borrow_index = market.borrow_index;
        let threshold = market.liquidation_threshold_bps;

        let position = BorrowPosition::new(
            borrower,
            borrow_asset_id,
            amount,
            collateral,
            borrow_index,
            self.current_block,
            threshold,
        );

        // Verify the position is healthy before allowing the borrow
        if !position.is_healthy() {
            return Err(LendingError::InsufficientCollateral {
                health_factor_bps: position.health_factor_bps(),
            });
        }

        let position_id = position.id;

        // Update market
        let market = self.get_market_mut(borrow_asset_id).unwrap();
        market.total_borrows += amount;

        self.borrow_positions.push(position);
        Ok(position_id)
    }

    /// Repay a portion (or all) of a borrow position's debt.
    ///
    /// Returns the actual amount repaid.
    pub fn repay(&mut self, position_id: &[u8; 32], amount: u64) -> Result<u64, LendingError> {
        let pos_idx = self
            .borrow_positions
            .iter()
            .position(|p| &p.id == position_id)
            .ok_or(LendingError::PositionNotFound)?;

        if self.borrow_positions[pos_idx].repaid {
            return Err(LendingError::AlreadyRepaid);
        }

        let actual = self.borrow_positions[pos_idx].repay(amount);
        let borrow_asset_id = self.borrow_positions[pos_idx].borrow_asset_id;

        // Update market
        if let Some(market) = self.get_market_mut(borrow_asset_id) {
            market.total_borrows = market.total_borrows.saturating_sub(actual);
        }

        Ok(actual)
    }

    /// Attempt to liquidate an unhealthy borrow position.
    pub fn liquidate(
        &mut self,
        position_id: &[u8; 32],
        liquidator: CellId,
        repay_amount: u64,
        collateral_asset_id: u64,
    ) -> Result<LiquidationResult, LendingError> {
        let engine = self.liquidation_engine.clone().unwrap_or_default();

        let pos_idx = self
            .borrow_positions
            .iter()
            .position(|p| &p.id == position_id)
            .ok_or(LendingError::PositionNotFound)?;

        let current_block = self.current_block;
        let result = engine.liquidate(
            &mut self.borrow_positions[pos_idx],
            liquidator,
            repay_amount,
            collateral_asset_id,
            current_block,
        );

        // Update market on successful liquidation
        if let LiquidationResult::Success(ref receipt) = result {
            let borrow_asset_id = self.borrow_positions[pos_idx].borrow_asset_id;
            if let Some(market) = self.get_market_mut(borrow_asset_id) {
                market.total_borrows = market.total_borrows.saturating_sub(receipt.debt_repaid);
            }
        }

        Ok(result)
    }
}

// =============================================================================
// Errors
// =============================================================================

/// Errors from lending pool operations.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum LendingError {
    /// Market for this asset doesn't exist.
    MarketNotFound { asset_id: u64 },
    /// Market is not currently active.
    MarketInactive { asset_id: u64 },
    /// Not enough liquidity in the pool.
    InsufficientLiquidity { available: u64, requested: u64 },
    /// Collateral insufficient for the borrow.
    InsufficientCollateral { health_factor_bps: u64 },
    /// Position not found.
    PositionNotFound,
    /// Supply position already withdrawn.
    AlreadyWithdrawn,
    /// Borrow position already repaid.
    AlreadyRepaid,
}

impl std::fmt::Display for LendingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MarketNotFound { asset_id } => {
                write!(f, "market not found for asset {}", asset_id)
            }
            Self::MarketInactive { asset_id } => {
                write!(f, "market inactive for asset {}", asset_id)
            }
            Self::InsufficientLiquidity {
                available,
                requested,
            } => write!(
                f,
                "insufficient liquidity: {} available, {} requested",
                available, requested
            ),
            Self::InsufficientCollateral { health_factor_bps } => write!(
                f,
                "insufficient collateral: health factor {} bps",
                health_factor_bps
            ),
            Self::PositionNotFound => write!(f, "position not found"),
            Self::AlreadyWithdrawn => write!(f, "position already withdrawn"),
            Self::AlreadyRepaid => write!(f, "position already repaid"),
        }
    }
}

impl std::error::Error for LendingError {}

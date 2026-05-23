//! `pyana-amm`: Constant-product automated market maker for pyana.
//!
//! # Architecture
//!
//! ```text
//! ┌───────────────────────────────────────────────────────┐
//! │  AMM Pool (HOSTED cell)                                │
//! │  ┌─────────────────────────────────────────────────┐  │
//! │  │  reserve_a, reserve_b, k = reserve_a * reserve_b│  │
//! │  │  lp_total_supply, fee_bps = 30 (0.3%)          │  │
//! │  └─────────────────────────────────────────────────┘  │
//! └───────────────────────────────────────────────────────┘
//!         │                     │                    │
//!    ┌────┴───┐           ┌────┴────┐         ┌────┴────┐
//!    │  Swap  │           │Add Liq. │         │Rem. Liq.│
//!    │ (Turn) │           │ (Turn)  │         │ (Turn)  │
//!    └────────┘           └─────────┘         └─────────┘
//! ```
//!
//! Pool state lives in HOSTED cells. Operations use `TurnComposer` for atomic
//! execution. The swap circuit proves the constant-product invariant is maintained.
//!
//! # Modules
//!
//! - [`pool`]: Core liquidity pool state and operations
//! - [`circuit`]: STARK circuit descriptors for swap and liquidity proofs
//! - [`lp_token`]: LP token minting/burning via the note model
//! - [`router`]: Multi-hop swap routing (A -> B -> C)

pub mod circuit;
pub mod lp_token;
pub mod pool;
pub mod router;
pub mod server;

#[cfg(test)]
mod tests;

use std::collections::HashMap;

use pool::{LiquidityPool, PoolId};

// =============================================================================
// AMM Registry
// =============================================================================

/// Registry of all liquidity pools managed by this AMM instance.
#[derive(Clone, Debug, Default)]
pub struct AmmRegistry {
    /// Pools indexed by their content-addressed ID.
    pools: HashMap<PoolId, LiquidityPool>,
    /// Index: asset pair -> pool ID for fast lookup.
    pair_index: HashMap<(u64, u64), PoolId>,
}

impl AmmRegistry {
    /// Create a new empty registry.
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a new pool in the registry.
    pub fn register_pool(&mut self, pool: LiquidityPool) {
        let id = pool.id;
        self.pair_index.insert((pool.asset_a, pool.asset_b), id);
        self.pair_index.insert((pool.asset_b, pool.asset_a), id);
        self.pools.insert(id, pool);
    }

    /// Look up a pool by ID.
    pub fn get_pool(&self, id: &PoolId) -> Option<&LiquidityPool> {
        self.pools.get(id)
    }

    /// Look up a pool by ID (mutable).
    pub fn get_pool_mut(&mut self, id: &PoolId) -> Option<&mut LiquidityPool> {
        self.pools.get_mut(id)
    }

    /// Find a pool by asset pair.
    pub fn find_pool_by_pair(&self, asset_a: u64, asset_b: u64) -> Option<&LiquidityPool> {
        self.pair_index
            .get(&(asset_a, asset_b))
            .and_then(|id| self.pools.get(id))
    }

    /// Find a pool by asset pair (mutable).
    pub fn find_pool_by_pair_mut(
        &mut self,
        asset_a: u64,
        asset_b: u64,
    ) -> Option<&mut LiquidityPool> {
        let id = self.pair_index.get(&(asset_a, asset_b)).copied()?;
        self.pools.get_mut(&id)
    }

    /// Get all pools as a slice (for routing).
    pub fn all_pools(&self) -> Vec<&LiquidityPool> {
        self.pools.values().collect()
    }

    /// Number of registered pools.
    pub fn pool_count(&self) -> usize {
        self.pools.len()
    }
}

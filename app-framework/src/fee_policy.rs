//! Multi-asset fee configuration for pyana apps.
//!
//! `FeePolicy` lets an app declare which assets it accepts as fee payment and
//! at what rate relative to a base fee denominated in the native computron
//! asset. Apps call `compute_fee` on the policy to price a given operation for
//! a given paying asset, without any external primitive to wrap — this module
//! is self-contained configuration logic.
//!
//! # Triage (2026-05-24)
//!
//! Load-bearing. The fee-pricing logic is pure configuration —
//! no executor / ledger coupling — and the storage→cell-program
//! migration does not touch this surface. Apps that price multiple
//! payment assets (gallery's royalty splits, compute-exchange's
//! buyer-pays-in-tier-token, subscription's per-tier pricing) all
//! need exactly this shape. Kept as-is; install via
//! `AppServer::with_fee_policy(FeePolicy)` so handlers extract it
//! via `axum::Extension<FeePolicy>`.
//!
//! Verdict: **load-bearing, no updates needed**.
//!
//! # Usage
//!
//! ```ignore
//! use pyana_app_framework::fee_policy::{FeePolicy};
//!
//! let policy = FeePolicy::computrons_only()
//!     .with_asset(some_stablecoin_id, 11000, 500); // 10% premium, 500 minimum
//!
//! if let Some(fee) = policy.compute_fee(&paying_asset, base_fee) {
//!     // accept payment
//! }
//! ```

use serde::{Deserialize, Serialize};

/// Asset identifier re-exported from the intent crate so apps have a single import.
pub type AssetId = pyana_intent::exchange::AssetId;

/// The native platform asset sentinel: all-zero bytes.
pub const NATIVE_ASSET: AssetId = [0u8; 32];

/// A single accepted asset with its fee multiplier and minimum.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AcceptedAsset {
    /// The asset this entry describes.
    pub asset: AssetId,
    /// Multiplier relative to base fee, in basis points.
    /// 10_000 = par (same as base). 12_000 = 20% more expensive.
    pub fee_bps: u32,
    /// Minimum fee in this asset regardless of computed amount.
    pub min_fee: u64,
}

/// Multi-asset fee configuration.
///
/// Every app starts with `computrons_only()` (the native asset at par) and can
/// add additional accepted assets with `with_asset`. The policy is stored as an
/// axum Extension layer so handlers can read it without additional state.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct FeePolicy {
    /// Ordered list of accepted assets (first match wins when an asset appears
    /// multiple times, though `with_asset` only adds; it never de-dupes).
    pub accepted: Vec<AcceptedAsset>,
    /// The asset that serves as the base for fee calculations.
    pub default_asset: AssetId,
}

impl FeePolicy {
    /// Accept only the native computron asset at a 1:1 rate (10_000 bps).
    pub fn computrons_only() -> Self {
        Self {
            accepted: vec![AcceptedAsset {
                asset: NATIVE_ASSET,
                fee_bps: 10_000,
                min_fee: 0,
            }],
            default_asset: NATIVE_ASSET,
        }
    }

    /// Add another accepted asset to this policy (builder method).
    ///
    /// * `fee_bps` — fee multiplier in basis points (10_000 = par with base).
    /// * `min_fee` — minimum fee denominated in `asset`.
    pub fn with_asset(mut self, asset: AssetId, fee_bps: u32, min_fee: u64) -> Self {
        self.accepted.push(AcceptedAsset {
            asset,
            fee_bps,
            min_fee,
        });
        self
    }

    /// Return `true` if `asset` is in the accepted list.
    pub fn accepts(&self, asset: &AssetId) -> bool {
        self.accepted.iter().any(|a| &a.asset == asset)
    }

    /// Compute the fee for `asset` given a `base_amount` (in native computrons).
    ///
    /// Returns `None` if the asset is not accepted.
    /// Returns `Some(fee)` where `fee = max(min_fee, base_amount * fee_bps / 10_000)`.
    pub fn compute_fee(&self, asset: &AssetId, base_amount: u64) -> Option<u64> {
        let entry = self.accepted.iter().find(|a| &a.asset == asset)?;
        let scaled = (base_amount as u128).saturating_mul(entry.fee_bps as u128) / 10_000;
        let fee = (scaled as u64).max(entry.min_fee);
        Some(fee)
    }
}

impl Default for FeePolicy {
    fn default() -> Self {
        Self::computrons_only()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn native_asset_at_par() {
        let policy = FeePolicy::computrons_only();
        assert!(policy.accepts(&NATIVE_ASSET));
        assert_eq!(policy.compute_fee(&NATIVE_ASSET, 1000), Some(1000));
    }

    #[test]
    fn premium_asset_and_min_fee() {
        let alt = [0xAA; 32];
        let policy = FeePolicy::computrons_only().with_asset(alt, 12_000, 500);
        // base=100 → 100 * 12000 / 10000 = 120, but min=500 → 500
        assert_eq!(policy.compute_fee(&alt, 100), Some(500));
        // base=10_000 → 10000 * 12000 / 10000 = 12_000 > 500 → 12_000
        assert_eq!(policy.compute_fee(&alt, 10_000), Some(12_000));
    }

    #[test]
    fn unaccepted_asset_returns_none() {
        let policy = FeePolicy::computrons_only();
        let unknown = [0xFF; 32];
        assert_eq!(policy.compute_fee(&unknown, 100), None);
        assert!(!policy.accepts(&unknown));
    }
}

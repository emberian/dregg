//! Multi-asset fee support for stablecoin mint and stability-fee operations.
//!
//! Exposes:
//! - A [`FeePolicyExt`] trait that adds `compute_fee_for_asset` convenience.
//! - A `GET /fees` handler returning the current policy as JSON.
//! - Modified mint and stability-fee request types that accept an optional
//!   `paying_asset` field.
//!
//! # Accepted Assets
//!
//! The default policy is configured as:
//! ```text
//! FeePolicy::computrons_only()
//!     .with_asset(PUSD_ASSET,  10_000, 100)   // PUSD at par, min 100
//!     .with_asset(ETH_ASSET,   11_000,  50)   // ETH at 10% premium, min 50
//! ```
//!
//! `PUSD_ASSET` and `ETH_ASSET` are 32-byte identifiers derived from the CDP
//! asset type constants (`PUSD_ASSET_TYPE` and `ETH_ASSET_TYPE`) left-padded
//! to 32 bytes.

use axum::{Extension, Json, http::StatusCode};
use serde::{Deserialize, Serialize};

use pyana_app_framework::fee_policy::{AcceptedAsset, AssetId, FeePolicy};

use crate::cdp::{ETH_ASSET_TYPE, PUSD_ASSET_TYPE};

// =============================================================================
// Asset IDs (32-byte identifiers derived from the CDP u64 asset type codes)
// =============================================================================

/// 32-byte asset ID for PUSD, derived from PUSD_ASSET_TYPE.
pub fn pusd_asset_id() -> AssetId {
    let mut id = [0u8; 32];
    id[24..].copy_from_slice(&PUSD_ASSET_TYPE.to_be_bytes());
    id
}

/// 32-byte asset ID for ETH collateral, derived from ETH_ASSET_TYPE.
pub fn eth_asset_id() -> AssetId {
    let mut id = [0u8; 32];
    id[24..].copy_from_slice(&ETH_ASSET_TYPE.to_be_bytes());
    id
}

// =============================================================================
// Default fee policy
// =============================================================================

/// Build the default multi-asset fee policy for the stablecoin system.
///
/// - Native computrons: par (10_000 bps), no minimum.
/// - PUSD: par (10_000 bps), minimum 100 units.
/// - ETH: 10% premium (11_000 bps), minimum 50 units.
pub fn default_fee_policy() -> FeePolicy {
    FeePolicy::computrons_only()
        .with_asset(pusd_asset_id(), 10_000, 100)
        .with_asset(eth_asset_id(), 11_000, 50)
}

// =============================================================================
// GET /fees handler
// =============================================================================

/// Response from `GET /fees`.
#[derive(Serialize)]
pub struct FeePolicyResponse {
    pub accepted_assets: Vec<AcceptedAssetJson>,
    pub default_asset: String,
}

/// JSON-serializable view of an [`AcceptedAsset`].
#[derive(Serialize)]
pub struct AcceptedAssetJson {
    /// Hex-encoded 32-byte asset ID.
    pub asset: String,
    /// Fee multiplier in basis points.
    pub fee_bps: u32,
    /// Minimum fee in this asset.
    pub min_fee: u64,
}

fn asset_to_hex(a: &AssetId) -> String {
    hex::encode(a)
}

/// `GET /fees` — return the current fee policy as JSON.
pub async fn get_fees(
    Extension(policy): Extension<FeePolicy>,
) -> Json<FeePolicyResponse> {
    Json(FeePolicyResponse {
        accepted_assets: policy
            .accepted
            .iter()
            .map(|a| AcceptedAssetJson {
                asset: asset_to_hex(&a.asset),
                fee_bps: a.fee_bps,
                min_fee: a.min_fee,
            })
            .collect(),
        default_asset: asset_to_hex(&policy.default_asset),
    })
}

// =============================================================================
// Fee computation helpers
// =============================================================================

/// Hex-encode a 32-byte asset ID.
pub fn hex_to_asset(s: &str) -> Option<AssetId> {
    if s.len() != 64 {
        return None;
    }
    let bytes = hex::decode(s).ok()?;
    bytes.try_into().ok()
}

/// Resolve an optional `paying_asset` hex string to an `AssetId`.
/// Returns the policy default asset if `paying_asset` is `None`.
pub fn resolve_paying_asset(
    paying_asset: Option<&str>,
    policy: &FeePolicy,
) -> Result<AssetId, String> {
    match paying_asset {
        None => Ok(policy.default_asset),
        Some(s) => hex_to_asset(s).ok_or_else(|| format!("invalid paying_asset hex: {s}")),
    }
}

/// Compute the fee for a given asset and base amount, returning an HTTP error
/// if the asset is not accepted by the policy.
pub fn compute_fee_or_reject(
    policy: &FeePolicy,
    asset: &AssetId,
    base_amount: u64,
) -> Result<u64, (StatusCode, Json<pyana_app_framework::server::ErrorResponse>)> {
    policy
        .compute_fee(asset, base_amount)
        .ok_or_else(|| {
            pyana_app_framework::server::api_error(
                StatusCode::BAD_REQUEST,
                format!(
                    "asset {} is not accepted for fee payment",
                    hex::encode(asset)
                ),
            )
        })
}

// =============================================================================
// Hex helpers
// =============================================================================

mod hex {
    pub fn encode(b: &[u8]) -> String {
        b.iter().map(|byte| format!("{byte:02x}")).collect()
    }

    pub fn decode(s: &str) -> Result<Vec<u8>, ()> {
        if s.len() % 2 != 0 {
            return Err(());
        }
        (0..s.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&s[i..i + 2], 16).map_err(|_| ()))
            .collect()
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_app_framework::fee_policy::NATIVE_ASSET;

    // ---- Upgrade 2, Test 1: default policy accepts PUSD and ETH ---
    #[test]
    fn default_policy_accepts_pusd_and_eth() {
        let policy = default_fee_policy();
        assert!(policy.accepts(&NATIVE_ASSET), "should accept native computrons");
        assert!(policy.accepts(&pusd_asset_id()), "should accept PUSD");
        assert!(policy.accepts(&eth_asset_id()), "should accept ETH");
    }

    // ---- Upgrade 2, Test 2: fee computation for each accepted asset ---
    #[test]
    fn fee_computation_for_accepted_assets() {
        let policy = default_fee_policy();
        let base = 10_000u64;

        // Native at par: 10_000 * 10_000 / 10_000 = 10_000
        let native_fee = policy.compute_fee(&NATIVE_ASSET, base).unwrap();
        assert_eq!(native_fee, 10_000);

        // PUSD at par (10_000 bps), min 100: same as native
        let pusd_fee = policy.compute_fee(&pusd_asset_id(), base).unwrap();
        assert_eq!(pusd_fee, 10_000);

        // ETH at 11_000 bps (10% premium): 10_000 * 11_000 / 10_000 = 11_000
        let eth_fee = policy.compute_fee(&eth_asset_id(), base).unwrap();
        assert_eq!(eth_fee, 11_000);
    }

    // ---- Upgrade 2, Test 3: unknown asset returns None ---
    #[test]
    fn unknown_asset_returns_none() {
        let policy = default_fee_policy();
        let unknown = [0xFF; 32];
        assert!(policy.compute_fee(&unknown, 1000).is_none());
        assert!(!policy.accepts(&unknown));
    }

    // ---- Upgrade 2, Test 4: minimum fee is enforced ---
    #[test]
    fn minimum_fee_enforced_for_small_amounts() {
        let policy = default_fee_policy();

        // PUSD min_fee = 100; base=1 → computed=1, but min kicks in → 100
        let fee = policy.compute_fee(&pusd_asset_id(), 1).unwrap();
        assert_eq!(fee, 100, "PUSD min_fee should be 100");

        // ETH min_fee = 50; base=1 → computed=1, but min kicks in → 50
        let fee = policy.compute_fee(&eth_asset_id(), 1).unwrap();
        assert_eq!(fee, 50, "ETH min_fee should be 50");
    }

    // ---- Upgrade 2, Test 5: resolve_paying_asset returns default when None ---
    #[test]
    fn resolve_paying_asset_default_when_none() {
        let policy = default_fee_policy();
        let asset = resolve_paying_asset(None, &policy).unwrap();
        assert_eq!(asset, NATIVE_ASSET);
    }

    // ---- Upgrade 2, Test 6: resolve_paying_asset parses hex correctly ---
    #[test]
    fn resolve_paying_asset_parses_hex() {
        let policy = default_fee_policy();
        let pusd_hex = hex::encode(&pusd_asset_id());
        let asset = resolve_paying_asset(Some(&pusd_hex), &policy).unwrap();
        assert_eq!(asset, pusd_asset_id());
    }

    // ---- Upgrade 2, Test 7: invalid hex returns error ---
    #[test]
    fn resolve_paying_asset_invalid_hex_errors() {
        let policy = default_fee_policy();
        let result = resolve_paying_asset(Some("notvalidhex"), &policy);
        assert!(result.is_err());
    }
}

//! Multi-asset fee denomination: services can accept fees in various tokens,
//! not just computrons.
//!
//! Exchange rates are maintained per-asset and validated for staleness.
//! The policy validates payments and converts to computron equivalents.

use std::collections::HashMap;

/// Asset identifier (content-addressed from token metadata).
pub type AssetId = [u8; 32];

/// The canonical computron asset (all-zeros by convention).
pub const COMPUTRON_ASSET: AssetId = [0u8; 32];

/// A multi-asset fee policy: services can accept fees in various tokens,
/// not just computrons.
#[derive(Debug, Clone)]
pub struct FeePolicy {
    /// Accepted denominations with exchange rates relative to computrons.
    pub accepted_assets: HashMap<AssetId, ExchangeRate>,
    /// If true, ONLY listed assets accepted (whitelist mode).
    /// If false, computrons always accepted as fallback.
    pub strict: bool,
}

/// Exchange rate for converting an asset to computrons.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExchangeRate {
    /// How many units of this asset equal 1 computron.
    /// (e.g., if 1 USDC = 100 computrons, then rate = 100).
    pub rate: u64,
    /// Rate last updated at this height (stale rates rejected).
    pub updated_at: u64,
    /// Maximum age of rate before it's considered stale (in block heights).
    pub max_age: u64,
}

/// A fee payment in any accepted denomination.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FeePayment {
    /// The asset being paid in.
    pub asset: AssetId,
    /// Amount of the asset being paid.
    pub amount: u64,
    /// Equivalent computron value (computed from exchange rate).
    pub computron_equivalent: u64,
}

/// Errors from fee validation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FeeError {
    /// The asset is not accepted by this policy.
    AssetNotAccepted { asset: AssetId },
    /// The exchange rate is stale (too old).
    StaleRate {
        asset: AssetId,
        updated_at: u64,
        current_height: u64,
        max_age: u64,
    },
    /// The computron equivalent in the payment doesn't match the rate.
    EquivalentMismatch {
        claimed: u64,
        computed: u64,
    },
    /// Payment amount is zero.
    ZeroAmount,
}

impl FeePolicy {
    /// Create a policy that only accepts computrons.
    pub fn computrons_only() -> Self {
        let mut accepted = HashMap::new();
        accepted.insert(
            COMPUTRON_ASSET,
            ExchangeRate {
                rate: 1, // 1:1 by definition.
                updated_at: 0,
                max_age: u64::MAX, // Computron rate never stales.
            },
        );
        Self {
            accepted_assets: accepted,
            strict: true,
        }
    }

    /// Create a multi-asset policy from a list of (asset, rate) pairs.
    /// Computrons are always implicitly accepted unless strict mode is enabled
    /// via `set_strict`.
    pub fn multi_asset(assets: Vec<(AssetId, ExchangeRate)>) -> Self {
        let mut accepted: HashMap<AssetId, ExchangeRate> = assets.into_iter().collect();
        // Always include computrons at 1:1 unless explicitly overridden.
        accepted.entry(COMPUTRON_ASSET).or_insert(ExchangeRate {
            rate: 1,
            updated_at: 0,
            max_age: u64::MAX,
        });
        Self {
            accepted_assets: accepted,
            strict: false,
        }
    }

    /// Set strict mode. In strict mode, ONLY listed assets are accepted.
    pub fn set_strict(&mut self, strict: bool) {
        self.strict = strict;
    }

    /// Validate a fee payment against this policy.
    ///
    /// Checks:
    /// 1. The asset is in the accepted set (or computrons as fallback in non-strict mode).
    /// 2. The exchange rate is not stale.
    /// 3. The claimed computron_equivalent matches the actual conversion.
    ///
    /// Returns the validated computron equivalent on success.
    pub fn validate_payment(
        &self,
        payment: &FeePayment,
        current_height: u64,
    ) -> Result<u64, FeeError> {
        if payment.amount == 0 {
            return Err(FeeError::ZeroAmount);
        }

        let rate = self.get_rate(&payment.asset)?;

        // Check staleness.
        if current_height > rate.updated_at + rate.max_age {
            return Err(FeeError::StaleRate {
                asset: payment.asset,
                updated_at: rate.updated_at,
                current_height,
                max_age: rate.max_age,
            });
        }

        // Compute the expected computron equivalent.
        let computed = self.compute_equivalent(payment.amount, rate);

        // Verify the claimed equivalent matches.
        if payment.computron_equivalent != computed {
            return Err(FeeError::EquivalentMismatch {
                claimed: payment.computron_equivalent,
                computed,
            });
        }

        Ok(computed)
    }

    /// Convert an amount in any accepted asset to computron equivalent.
    pub fn to_computrons(
        &self,
        asset: &AssetId,
        amount: u64,
        current_height: u64,
    ) -> Result<u64, FeeError> {
        if amount == 0 {
            return Err(FeeError::ZeroAmount);
        }

        let rate = self.get_rate(asset)?;

        // Check staleness.
        if current_height > rate.updated_at + rate.max_age {
            return Err(FeeError::StaleRate {
                asset: *asset,
                updated_at: rate.updated_at,
                current_height,
                max_age: rate.max_age,
            });
        }

        Ok(self.compute_equivalent(amount, rate))
    }

    /// Update the exchange rate for an asset.
    pub fn update_rate(&mut self, asset: AssetId, rate: ExchangeRate) {
        self.accepted_assets.insert(asset, rate);
    }

    /// Check if an asset is accepted.
    pub fn accepts(&self, asset: &AssetId) -> bool {
        if self.accepted_assets.contains_key(asset) {
            return true;
        }
        // In non-strict mode, computrons are always accepted.
        if !self.strict && *asset == COMPUTRON_ASSET {
            return true;
        }
        false
    }

    /// Get the exchange rate for an asset.
    fn get_rate(&self, asset: &AssetId) -> Result<&ExchangeRate, FeeError> {
        if let Some(rate) = self.accepted_assets.get(asset) {
            return Ok(rate);
        }

        // In non-strict mode, computrons are always accepted at 1:1.
        if !self.strict && *asset == COMPUTRON_ASSET {
            // This shouldn't happen because multi_asset() always includes computrons,
            // but handle it defensively.
            return Err(FeeError::AssetNotAccepted { asset: *asset });
        }

        Err(FeeError::AssetNotAccepted { asset: *asset })
    }

    /// Compute the computron equivalent for a given amount at a given rate.
    /// Formula: computron_equivalent = amount * rate
    /// (rate = how many computrons 1 unit of this asset is worth).
    fn compute_equivalent(&self, amount: u64, rate: &ExchangeRate) -> u64 {
        amount.saturating_mul(rate.rate)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn usdc_asset() -> AssetId {
        *blake3::hash(b"USDC").as_bytes()
    }

    fn eth_asset() -> AssetId {
        *blake3::hash(b"ETH").as_bytes()
    }

    #[test]
    fn computrons_only_policy_accepts_computrons() {
        let policy = FeePolicy::computrons_only();
        let payment = FeePayment {
            asset: COMPUTRON_ASSET,
            amount: 1000,
            computron_equivalent: 1000, // 1:1
        };

        let result = policy.validate_payment(&payment, 100);
        assert_eq!(result, Ok(1000));
    }

    #[test]
    fn computrons_only_rejects_other_assets() {
        let policy = FeePolicy::computrons_only();
        let payment = FeePayment {
            asset: usdc_asset(),
            amount: 100,
            computron_equivalent: 10_000,
        };

        let result = policy.validate_payment(&payment, 100);
        assert!(matches!(result, Err(FeeError::AssetNotAccepted { .. })));
    }

    #[test]
    fn multi_asset_with_exchange_rates() {
        let usdc = usdc_asset();
        let policy = FeePolicy::multi_asset(vec![(
            usdc,
            ExchangeRate {
                rate: 100, // 1 USDC = 100 computrons
                updated_at: 50,
                max_age: 100,
            },
        )]);

        let payment = FeePayment {
            asset: usdc,
            amount: 10,
            computron_equivalent: 1000, // 10 * 100
        };

        let result = policy.validate_payment(&payment, 80);
        assert_eq!(result, Ok(1000));
    }

    #[test]
    fn stale_rate_rejected() {
        let usdc = usdc_asset();
        let policy = FeePolicy::multi_asset(vec![(
            usdc,
            ExchangeRate {
                rate: 100,
                updated_at: 50,
                max_age: 20, // Rate valid until height 70.
            },
        )]);

        let payment = FeePayment {
            asset: usdc,
            amount: 10,
            computron_equivalent: 1000,
        };

        // At height 71 (> 50 + 20), the rate is stale.
        let result = policy.validate_payment(&payment, 71);
        assert!(matches!(result, Err(FeeError::StaleRate { .. })));

        // At height 70 (== 50 + 20), still valid.
        let result = policy.validate_payment(&payment, 70);
        assert_eq!(result, Ok(1000));
    }

    #[test]
    fn strict_mode_rejects_unlisted_assets() {
        let usdc = usdc_asset();
        let eth = eth_asset();
        let mut policy = FeePolicy::multi_asset(vec![(
            usdc,
            ExchangeRate {
                rate: 100,
                updated_at: 0,
                max_age: 1000,
            },
        )]);
        policy.set_strict(true);

        // ETH is not listed.
        let payment = FeePayment {
            asset: eth,
            amount: 1,
            computron_equivalent: 5000,
        };

        let result = policy.validate_payment(&payment, 50);
        assert!(matches!(result, Err(FeeError::AssetNotAccepted { .. })));
    }

    #[test]
    fn non_strict_mode_always_accepts_computrons() {
        // Even if computrons aren't explicitly listed, non-strict accepts them.
        let policy = FeePolicy::multi_asset(vec![]); // Only computrons via default.

        let payment = FeePayment {
            asset: COMPUTRON_ASSET,
            amount: 500,
            computron_equivalent: 500,
        };

        let result = policy.validate_payment(&payment, 0);
        assert_eq!(result, Ok(500));
    }

    #[test]
    fn equivalent_mismatch_detected() {
        let usdc = usdc_asset();
        let policy = FeePolicy::multi_asset(vec![(
            usdc,
            ExchangeRate {
                rate: 100,
                updated_at: 0,
                max_age: 1000,
            },
        )]);

        let payment = FeePayment {
            asset: usdc,
            amount: 10,
            computron_equivalent: 999, // Should be 1000.
        };

        let result = policy.validate_payment(&payment, 50);
        assert_eq!(
            result,
            Err(FeeError::EquivalentMismatch {
                claimed: 999,
                computed: 1000,
            })
        );
    }

    #[test]
    fn to_computrons_conversion() {
        let eth = eth_asset();
        let policy = FeePolicy::multi_asset(vec![(
            eth,
            ExchangeRate {
                rate: 5000, // 1 ETH = 5000 computrons.
                updated_at: 100,
                max_age: 50,
            },
        )]);

        let result = policy.to_computrons(&eth, 3, 120);
        assert_eq!(result, Ok(15_000)); // 3 * 5000

        // Stale at height 151.
        let result = policy.to_computrons(&eth, 3, 151);
        assert!(matches!(result, Err(FeeError::StaleRate { .. })));
    }

    #[test]
    fn zero_amount_rejected() {
        let policy = FeePolicy::computrons_only();
        let payment = FeePayment {
            asset: COMPUTRON_ASSET,
            amount: 0,
            computron_equivalent: 0,
        };

        let result = policy.validate_payment(&payment, 0);
        assert_eq!(result, Err(FeeError::ZeroAmount));
    }
}

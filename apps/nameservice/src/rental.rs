//! Computron-based name rent and expiry.
//!
//! Names are rented, not owned forever. Shorter names cost more (premium pricing).
//! If rent lapses, there is a grace period before the name is released to the pool.

use serde::{Deserialize, Serialize};

use crate::registry::{GRACE_PERIOD_EPOCHS, NameEntry, NameRegistry, NameStatus, RegistryError};

// =============================================================================
// Rental Policy
// =============================================================================

/// Name rental cost tiers.
///
/// - 1-3 chars: 1000 computrons/epoch (premium)
/// - 4-7 chars: 100 computrons/epoch (standard-premium)
/// - 8+ chars: 10 computrons/epoch (base)
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RentalPolicy {
    /// Cost per epoch for names 8+ characters.
    pub base_rate: u64,
    /// Cost per epoch for names 4-7 characters.
    pub standard_premium_rate: u64,
    /// Cost per epoch for names 1-3 characters.
    pub premium_rate: u64,
    /// Grace period in epochs before expired names are released.
    pub grace_period: u64,
}

impl Default for RentalPolicy {
    fn default() -> Self {
        Self {
            base_rate: 10,
            standard_premium_rate: 100,
            premium_rate: 1000,
            grace_period: GRACE_PERIOD_EPOCHS,
        }
    }
}

impl RentalPolicy {
    /// Calculate the rent rate for a name based on its length.
    pub fn rate_for_name(&self, name: &str) -> u64 {
        let base_name = if name.contains('.') {
            // For hierarchical names, price by the leaf segment.
            name.split('.').next().unwrap_or(name)
        } else {
            name
        };

        match base_name.len() {
            0 => self.premium_rate, // should never happen due to validation
            1..=3 => self.premium_rate,
            4..=7 => self.standard_premium_rate,
            _ => self.base_rate,
        }
    }

    /// Calculate total cost for registering a name for N epochs.
    pub fn calculate_cost(&self, name: &str, epochs: u64) -> u64 {
        self.rate_for_name(name) * epochs
    }
}

// =============================================================================
// Rental Status
// =============================================================================

/// Rental status information for a name.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RentalStatus {
    /// The name.
    pub name: String,
    /// Current status (active, grace, expired).
    pub status: NameStatus,
    /// Epoch until which rent is paid.
    pub paid_until: u64,
    /// Rent rate per epoch.
    pub rate_per_epoch: u64,
    /// Total cost to renew for one additional epoch.
    pub renewal_cost_per_epoch: u64,
}

/// Get the rental status of a name.
pub fn rental_status(entry: &NameEntry, current_epoch: u64, policy: &RentalPolicy) -> RentalStatus {
    let status = if current_epoch <= entry.expires_at {
        NameStatus::Active {
            funded_until: entry.expires_at,
        }
    } else if current_epoch <= entry.expires_at + policy.grace_period {
        NameStatus::Grace {
            grace_expires: entry.expires_at + policy.grace_period,
        }
    } else {
        NameStatus::Expired
    };

    RentalStatus {
        name: entry.name.clone(),
        status,
        paid_until: entry.rent_paid_until,
        rate_per_epoch: entry.rent_rate,
        renewal_cost_per_epoch: policy.rate_for_name(&entry.name),
    }
}

/// Renew a name for additional epochs. Returns the updated entry.
pub async fn renew_name(
    registry: &NameRegistry,
    name: &str,
    caller: &[u8; 32],
    additional_epochs: u64,
    _available_computrons: u64,
    policy: &RentalPolicy,
) -> Result<NameEntry, RegistryError> {
    let cost = policy.calculate_cost(name, additional_epochs);
    if _available_computrons < cost {
        return Err(RegistryError::InsufficientFunds {
            required: cost,
            available: _available_computrons,
        });
    }

    registry.renew(name, caller, additional_epochs).await
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::registry::DelegationAuthority;

    #[test]
    fn premium_pricing_short_names() {
        let policy = RentalPolicy::default();

        // 1-3 char names: premium (1000/epoch)
        assert_eq!(policy.rate_for_name("a"), 1000);
        assert_eq!(policy.rate_for_name("ab"), 1000);
        assert_eq!(policy.rate_for_name("abc"), 1000);

        // 4-7 char names: standard premium (100/epoch)
        assert_eq!(policy.rate_for_name("abcd"), 100);
        assert_eq!(policy.rate_for_name("abcdefg"), 100);

        // 8+ char names: base (10/epoch)
        assert_eq!(policy.rate_for_name("abcdefgh"), 10);
        assert_eq!(policy.rate_for_name("my-long-name"), 10);
    }

    #[test]
    fn cost_calculation() {
        let policy = RentalPolicy::default();

        assert_eq!(policy.calculate_cost("abc", 10), 10_000); // 1000 * 10
        assert_eq!(policy.calculate_cost("alice", 100), 10_000); // 100 * 100
        assert_eq!(policy.calculate_cost("my-service", 100), 1_000); // 10 * 100
    }

    #[test]
    fn rental_status_active() {
        let policy = RentalPolicy::default();
        let entry = NameEntry {
            name: "alice".into(),
            target: "pyana://x".into(),
            owner: [0x01; 32],
            registered_at: 100,
            expires_at: 200,
            delegation: DelegationAuthority::None,
            version: 1,
            rent_paid_until: 200,
            rent_rate: 100,
        };

        let status = rental_status(&entry, 150, &policy);
        assert!(matches!(
            status.status,
            NameStatus::Active { funded_until: 200 }
        ));
    }

    #[test]
    fn rental_status_grace() {
        let policy = RentalPolicy::default();
        let entry = NameEntry {
            name: "alice".into(),
            target: "pyana://x".into(),
            owner: [0x01; 32],
            registered_at: 100,
            expires_at: 200,
            delegation: DelegationAuthority::None,
            version: 1,
            rent_paid_until: 200,
            rent_rate: 100,
        };

        let status = rental_status(&entry, 205, &policy);
        assert!(matches!(status.status, NameStatus::Grace { .. }));
    }

    #[test]
    fn rental_status_expired() {
        let policy = RentalPolicy::default();
        let entry = NameEntry {
            name: "alice".into(),
            target: "pyana://x".into(),
            owner: [0x01; 32],
            registered_at: 100,
            expires_at: 200,
            delegation: DelegationAuthority::None,
            version: 1,
            rent_paid_until: 200,
            rent_rate: 100,
        };

        let status = rental_status(&entry, 211, &policy);
        assert!(matches!(status.status, NameStatus::Expired));
    }

    #[tokio::test]
    async fn renewal_extends_expiry() {
        let registry = NameRegistry::new();
        let owner = [0x01; 32];
        let policy = RentalPolicy::default();

        registry
            .register(
                "my-service",
                "pyana://x".into(),
                owner,
                DelegationAuthority::None,
                100,
                50,
                policy.rate_for_name("my-service"),
            )
            .await
            .unwrap();

        // Renew for 20 more epochs
        let entry = renew_name(&registry, "my-service", &owner, 20, 10_000, &policy)
            .await
            .unwrap();

        assert_eq!(entry.expires_at, 170); // 150 + 20
        assert_eq!(entry.rent_paid_until, 170);
    }

    #[tokio::test]
    async fn renewal_insufficient_funds() {
        let registry = NameRegistry::new();
        let owner = [0x01; 32];
        let policy = RentalPolicy::default();

        registry
            .register(
                "abc",
                "pyana://x".into(),
                owner,
                DelegationAuthority::None,
                100,
                50,
                1000,
            )
            .await
            .unwrap();

        // Renew for 10 epochs costs 10_000, but only have 5_000
        let err = renew_name(&registry, "abc", &owner, 10, 5_000, &policy)
            .await
            .unwrap_err();

        assert!(matches!(err, RegistryError::InsufficientFunds { .. }));
    }
}

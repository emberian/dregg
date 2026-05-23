//! Sub-delegation: *.alice.* owned by alice.
//!
//! When a name is registered with DelegationAuthority::SubPrefix, the owner can
//! create sub-names under their prefix without governance votes. Non-owners must
//! get the owner's signature (simulated here by passing the owner key).

use crate::registry::{DelegationAuthority, NameEntry, NameRegistry, PyanaUri, RegistryError};
use crate::rental::RentalPolicy;

// =============================================================================
// Delegation
// =============================================================================

/// Register a sub-name under a delegated parent.
///
/// The sub-name is stored as "child.parent" in the registry.
/// Authorization: caller must be the owner of the parent name that has
/// SubPrefix or Full delegation authority.
pub async fn register_subname(
    registry: &NameRegistry,
    parent_name: &str,
    child_label: &str,
    target: PyanaUri,
    caller: &[u8; 32],
    current_epoch: u64,
    rental_epochs: u64,
    policy: &RentalPolicy,
) -> Result<NameEntry, RegistryError> {
    // Look up the parent to verify delegation authority.
    let parent = registry
        .lookup(parent_name, current_epoch)
        .await
        .ok_or_else(|| RegistryError::NotFound(parent_name.to_string()))?;

    // Verify caller is the owner of the parent.
    if &parent.owner != caller {
        return Err(RegistryError::Unauthorized(format!(
            "caller does not own parent name '{parent_name}'"
        )));
    }

    // Verify parent has delegation authority.
    match &parent.delegation {
        DelegationAuthority::None => {
            return Err(RegistryError::Unauthorized(format!(
                "name '{parent_name}' does not have delegation authority"
            )));
        }
        DelegationAuthority::SubPrefix { prefix } => {
            // SubPrefix authority: the prefix must match the parent name.
            if prefix != parent_name {
                return Err(RegistryError::Unauthorized(format!(
                    "delegation prefix '{prefix}' does not match parent '{parent_name}'"
                )));
            }
        }
        DelegationAuthority::Full => {
            // Full authority: can create any sub-name.
        }
    }

    // Construct the full sub-name: "child.parent"
    let full_name = format!("{child_label}.{parent_name}");
    let rent_rate = policy.rate_for_name(&full_name);

    // Register the sub-name. Owner is the same as the parent owner.
    registry
        .register(
            &full_name,
            target,
            *caller,
            DelegationAuthority::None,
            current_epoch,
            rental_epochs,
            rent_rate,
        )
        .await
}

/// Check whether a caller has delegation authority over a parent name.
pub async fn has_delegation_authority(
    registry: &NameRegistry,
    parent_name: &str,
    caller: &[u8; 32],
    current_epoch: u64,
) -> bool {
    if let Some(parent) = registry.lookup(parent_name, current_epoch).await {
        if &parent.owner != caller {
            return false;
        }
        !matches!(parent.delegation, DelegationAuthority::None)
    } else {
        false
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn owner_creates_subname() {
        let registry = NameRegistry::new();
        let owner = [0x01; 32];
        let policy = RentalPolicy::default();

        // Register "alice" with sub-prefix delegation.
        registry
            .register(
                "alice",
                "pyana://fed/alice/swiss".into(),
                owner,
                DelegationAuthority::SubPrefix {
                    prefix: "alice".into(),
                },
                100,
                50,
                100,
            )
            .await
            .unwrap();

        // Alice creates "oracle.alice" as a sub-name.
        let entry = register_subname(
            &registry,
            "alice",
            "oracle",
            "pyana://fed/oracle/swiss".into(),
            &owner,
            100,
            50,
            &policy,
        )
        .await
        .unwrap();

        assert_eq!(entry.name, "oracle.alice");
        assert_eq!(entry.target, "pyana://fed/oracle/swiss");
        assert_eq!(entry.owner, owner);
    }

    #[tokio::test]
    async fn non_owner_cannot_create_subname() {
        let registry = NameRegistry::new();
        let owner = [0x01; 32];
        let interloper = [0x02; 32];
        let policy = RentalPolicy::default();

        registry
            .register(
                "alice",
                "pyana://fed/alice/swiss".into(),
                owner,
                DelegationAuthority::SubPrefix {
                    prefix: "alice".into(),
                },
                100,
                50,
                100,
            )
            .await
            .unwrap();

        // Non-owner tries to create a sub-name.
        let err = register_subname(
            &registry,
            "alice",
            "evil",
            "pyana://fed/evil/swiss".into(),
            &interloper,
            100,
            50,
            &policy,
        )
        .await
        .unwrap_err();

        assert!(matches!(err, RegistryError::Unauthorized(_)));
    }

    #[tokio::test]
    async fn no_delegation_authority_blocks_subnames() {
        let registry = NameRegistry::new();
        let owner = [0x01; 32];
        let policy = RentalPolicy::default();

        // Register "bob" WITHOUT delegation authority.
        registry
            .register(
                "bob",
                "pyana://fed/bob/swiss".into(),
                owner,
                DelegationAuthority::None,
                100,
                50,
                100,
            )
            .await
            .unwrap();

        // Owner tries to create sub-name but has no delegation.
        let err = register_subname(
            &registry,
            "bob",
            "service",
            "pyana://fed/service/swiss".into(),
            &owner,
            100,
            50,
            &policy,
        )
        .await
        .unwrap_err();

        assert!(matches!(err, RegistryError::Unauthorized(_)));
    }

    #[tokio::test]
    async fn full_delegation_allows_any_subname() {
        let registry = NameRegistry::new();
        let owner = [0x01; 32];
        let policy = RentalPolicy::default();

        registry
            .register(
                "corp",
                "pyana://fed/corp/swiss".into(),
                owner,
                DelegationAuthority::Full,
                100,
                50,
                100,
            )
            .await
            .unwrap();

        let entry = register_subname(
            &registry,
            "corp",
            "department-a",
            "pyana://fed/dept-a/swiss".into(),
            &owner,
            100,
            50,
            &policy,
        )
        .await
        .unwrap();

        assert_eq!(entry.name, "department-a.corp");
    }
}

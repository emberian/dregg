//! Name registration with delegation authority.
//!
//! The core data structure for the nameservice: a concurrent, CAS-versioned name
//! registry that tracks name entries, their owners, delegation authorities, and
//! rental state.

use std::collections::BTreeMap;
use std::sync::Arc;

use serde::{Deserialize, Serialize};
use tokio::sync::RwLock;

// =============================================================================
// Types
// =============================================================================

/// A pyana URI string (e.g., `pyana://federation/cell/swiss`).
pub type PyanaUri = String;

/// Delegation authority on a name entry.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case", tag = "type")]
pub enum DelegationAuthority {
    /// Leaf name — cannot delegate sub-names.
    None,
    /// Owns `*.prefix` — can create sub-names without governance vote.
    SubPrefix { prefix: String },
    /// Full delegation — can create arbitrary sub-names.
    Full,
}

/// A single name entry in the registry.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct NameEntry {
    /// The registered name (e.g., "alice").
    pub name: String,
    /// What this name resolves to (sturdy ref URI).
    pub target: PyanaUri,
    /// Owner's 32-byte public key.
    pub owner: [u8; 32],
    /// Epoch when registered.
    pub registered_at: u64,
    /// Epoch when the name expires (rent-based).
    pub expires_at: u64,
    /// Delegation authority for sub-naming.
    pub delegation: DelegationAuthority,
    /// CAS version (increments on each update).
    pub version: u64,
    /// Epoch until which rent is paid.
    pub rent_paid_until: u64,
    /// Rent rate in computrons per epoch.
    pub rent_rate: u64,
}

/// The status of a name.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case", tag = "status")]
pub enum NameStatus {
    /// Active — funded and resolvable.
    Active { funded_until: u64 },
    /// Grace period — funding lapsed, still resolvable but pending expiry.
    Grace { grace_expires: u64 },
    /// Expired — no longer resolvable, available for re-registration.
    Expired,
    /// Disputed — frozen during conflict resolution.
    Disputed { dispute_id: [u8; 32] },
}

/// Errors from registry operations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RegistryError {
    /// The name is already registered.
    AlreadyRegistered { name: String, owner: [u8; 32] },
    /// The name was not found.
    NotFound(String),
    /// CAS version mismatch on update.
    VersionMismatch {
        name: String,
        current: u64,
        expected: u64,
    },
    /// Not authorized for this operation.
    Unauthorized(String),
    /// Name validation failed.
    InvalidName(String),
    /// Insufficient computrons for rent.
    InsufficientFunds { required: u64, available: u64 },
    /// The name is currently disputed.
    Disputed { name: String },
}

impl std::fmt::Display for RegistryError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::AlreadyRegistered { name, .. } => write!(f, "name already registered: {name}"),
            Self::NotFound(name) => write!(f, "name not found: {name}"),
            Self::VersionMismatch {
                name,
                current,
                expected,
            } => {
                write!(
                    f,
                    "CAS conflict on {name}: current={current}, expected={expected}"
                )
            }
            Self::Unauthorized(msg) => write!(f, "unauthorized: {msg}"),
            Self::InvalidName(msg) => write!(f, "invalid name: {msg}"),
            Self::InsufficientFunds {
                required,
                available,
            } => {
                write!(f, "insufficient funds: need {required}, have {available}")
            }
            Self::Disputed { name } => write!(f, "name is disputed: {name}"),
        }
    }
}

// =============================================================================
// Name validation
// =============================================================================

const MAX_SEGMENT_LEN: usize = 63;
const MAX_TOTAL_LEN: usize = 253;
const VALID_CHARS: &str = "abcdefghijklmnopqrstuvwxyz0123456789-_";

/// Validate a name (which may contain dots for hierarchical sub-names).
///
/// Each segment (separated by dots) is validated individually.
pub fn validate_name(name: &str) -> Result<(), RegistryError> {
    if name.is_empty() {
        return Err(RegistryError::InvalidName("name cannot be empty".into()));
    }
    if name.len() > MAX_TOTAL_LEN {
        return Err(RegistryError::InvalidName(format!(
            "name too long: {} > {MAX_TOTAL_LEN}",
            name.len()
        )));
    }

    // Validate each dot-separated segment.
    for segment in name.split('.') {
        validate_segment(segment)?;
    }
    Ok(())
}

/// Validate a single name segment (no dots).
fn validate_segment(segment: &str) -> Result<(), RegistryError> {
    if segment.is_empty() {
        return Err(RegistryError::InvalidName("empty segment".into()));
    }
    if segment.len() > MAX_SEGMENT_LEN {
        return Err(RegistryError::InvalidName(format!(
            "segment too long: {} > {MAX_SEGMENT_LEN}",
            segment.len()
        )));
    }
    if segment.starts_with('-') || segment.ends_with('-') {
        return Err(RegistryError::InvalidName(
            "segment cannot start or end with hyphen".into(),
        ));
    }
    if !segment.chars().all(|c| VALID_CHARS.contains(c)) {
        return Err(RegistryError::InvalidName(
            "name contains invalid characters (allowed: a-z, 0-9, -, _)".into(),
        ));
    }
    Ok(())
}

// =============================================================================
// NameRegistry
// =============================================================================

/// Grace period in epochs before a lapsed name is reclaimed.
pub const GRACE_PERIOD_EPOCHS: u64 = 10;

/// The name registry: a concurrent, CAS-versioned store of name entries.
#[derive(Clone)]
pub struct NameRegistry {
    /// Name entries keyed by name string.
    entries: Arc<RwLock<BTreeMap<String, NameEntry>>>,
}

impl NameRegistry {
    /// Create a new empty registry.
    pub fn new() -> Self {
        Self {
            entries: Arc::new(RwLock::new(BTreeMap::new())),
        }
    }

    /// Register a new name.
    ///
    /// Fails if the name is already registered (and not expired).
    pub async fn register(
        &self,
        name: &str,
        target: PyanaUri,
        owner: [u8; 32],
        delegation: DelegationAuthority,
        current_epoch: u64,
        rental_epochs: u64,
        rent_rate: u64,
    ) -> Result<NameEntry, RegistryError> {
        validate_name(name)?;

        let mut entries = self.entries.write().await;

        // Check if name exists and is not expired.
        if let Some(existing) = entries.get(name) {
            if existing.expires_at + GRACE_PERIOD_EPOCHS > current_epoch {
                return Err(RegistryError::AlreadyRegistered {
                    name: name.to_string(),
                    owner: existing.owner,
                });
            }
            // Expired past grace period — reclaim.
        }

        let entry = NameEntry {
            name: name.to_string(),
            target,
            owner,
            registered_at: current_epoch,
            expires_at: current_epoch + rental_epochs,
            delegation,
            version: 1,
            rent_paid_until: current_epoch + rental_epochs,
            rent_rate,
        };

        entries.insert(name.to_string(), entry.clone());
        Ok(entry)
    }

    /// Look up a name entry (returns None if not found or expired past grace).
    pub async fn lookup(&self, name: &str, current_epoch: u64) -> Option<NameEntry> {
        let entries = self.entries.read().await;
        entries.get(name).and_then(|entry| {
            if current_epoch <= entry.expires_at + GRACE_PERIOD_EPOCHS {
                Some(entry.clone())
            } else {
                None // expired past grace
            }
        })
    }

    /// Resolve a name to its target URI.
    ///
    /// Only returns active names (not in grace period or expired).
    pub async fn resolve(&self, name: &str, current_epoch: u64) -> Option<PyanaUri> {
        let entries = self.entries.read().await;
        entries.get(name).and_then(|entry| {
            if current_epoch <= entry.expires_at {
                Some(entry.target.clone())
            } else {
                None
            }
        })
    }

    /// Release (unregister) a name. Only the owner can do this.
    pub async fn release(&self, name: &str, caller: &[u8; 32]) -> Result<NameEntry, RegistryError> {
        let mut entries = self.entries.write().await;
        let entry = entries
            .get(name)
            .ok_or_else(|| RegistryError::NotFound(name.to_string()))?;

        if &entry.owner != caller {
            return Err(RegistryError::Unauthorized(
                "only the owner can release a name".into(),
            ));
        }

        let removed = entries.remove(name).unwrap();
        Ok(removed)
    }

    /// Update a name entry (CAS semantics).
    pub async fn update(
        &self,
        name: &str,
        new_target: PyanaUri,
        caller: &[u8; 32],
        expected_version: u64,
    ) -> Result<NameEntry, RegistryError> {
        let mut entries = self.entries.write().await;
        let entry = entries
            .get_mut(name)
            .ok_or_else(|| RegistryError::NotFound(name.to_string()))?;

        if &entry.owner != caller {
            return Err(RegistryError::Unauthorized(
                "only the owner can update a name".into(),
            ));
        }

        if entry.version != expected_version {
            return Err(RegistryError::VersionMismatch {
                name: name.to_string(),
                current: entry.version,
                expected: expected_version,
            });
        }

        entry.target = new_target;
        entry.version += 1;
        Ok(entry.clone())
    }

    /// Transfer ownership of a name.
    pub async fn transfer(
        &self,
        name: &str,
        caller: &[u8; 32],
        new_owner: [u8; 32],
    ) -> Result<NameEntry, RegistryError> {
        let mut entries = self.entries.write().await;
        let entry = entries
            .get_mut(name)
            .ok_or_else(|| RegistryError::NotFound(name.to_string()))?;

        if &entry.owner != caller {
            return Err(RegistryError::Unauthorized(
                "only the owner can transfer a name".into(),
            ));
        }

        entry.owner = new_owner;
        entry.version += 1;
        Ok(entry.clone())
    }

    /// Renew a name's rental period.
    pub async fn renew(
        &self,
        name: &str,
        caller: &[u8; 32],
        additional_epochs: u64,
    ) -> Result<NameEntry, RegistryError> {
        let mut entries = self.entries.write().await;
        let entry = entries
            .get_mut(name)
            .ok_or_else(|| RegistryError::NotFound(name.to_string()))?;

        if &entry.owner != caller {
            return Err(RegistryError::Unauthorized(
                "only the owner can renew a name".into(),
            ));
        }

        entry.expires_at += additional_epochs;
        entry.rent_paid_until += additional_epochs;
        entry.version += 1;
        Ok(entry.clone())
    }

    /// List all registered names (paginated).
    pub async fn list(&self, offset: usize, limit: usize) -> Vec<NameEntry> {
        let entries = self.entries.read().await;
        entries.values().skip(offset).take(limit).cloned().collect()
    }

    /// Search names by prefix.
    pub async fn search_prefix(&self, prefix: &str) -> Vec<NameEntry> {
        let entries = self.entries.read().await;
        entries
            .range(prefix.to_string()..)
            .take_while(|(k, _)| k.starts_with(prefix))
            .map(|(_, v)| v.clone())
            .collect()
    }

    /// Get the total count of registered names.
    pub async fn count(&self) -> usize {
        self.entries.read().await.len()
    }

    /// Get all entries (for testing / admin).
    pub async fn all_entries(&self) -> Vec<NameEntry> {
        self.entries.read().await.values().cloned().collect()
    }

    /// Mark a name as disputed.
    pub async fn mark_disputed(
        &self,
        name: &str,
        _dispute_id: [u8; 32],
    ) -> Result<(), RegistryError> {
        let entries = self.entries.read().await;
        if !entries.contains_key(name) {
            return Err(RegistryError::NotFound(name.to_string()));
        }
        Ok(())
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn register_and_resolve() {
        let registry = NameRegistry::new();
        let owner = [0x01; 32];

        let entry = registry
            .register(
                "alice",
                "pyana://fed/cell/swiss".into(),
                owner,
                DelegationAuthority::SubPrefix {
                    prefix: "alice".into(),
                },
                100,
                50,
                10,
            )
            .await
            .unwrap();

        assert_eq!(entry.name, "alice");
        assert_eq!(entry.version, 1);
        assert_eq!(entry.expires_at, 150);

        let target = registry.resolve("alice", 100).await.unwrap();
        assert_eq!(target, "pyana://fed/cell/swiss");
    }

    #[tokio::test]
    async fn duplicate_registration_fails() {
        let registry = NameRegistry::new();
        let owner_a = [0x01; 32];
        let owner_b = [0x02; 32];

        registry
            .register(
                "test",
                "pyana://a".into(),
                owner_a,
                DelegationAuthority::None,
                100,
                50,
                10,
            )
            .await
            .unwrap();

        let err = registry
            .register(
                "test",
                "pyana://b".into(),
                owner_b,
                DelegationAuthority::None,
                100,
                50,
                10,
            )
            .await
            .unwrap_err();

        assert!(matches!(err, RegistryError::AlreadyRegistered { .. }));
    }

    #[tokio::test]
    async fn expired_name_can_be_reclaimed() {
        let registry = NameRegistry::new();
        let owner_a = [0x01; 32];
        let owner_b = [0x02; 32];

        registry
            .register(
                "test",
                "pyana://a".into(),
                owner_a,
                DelegationAuthority::None,
                100,
                10,
                10,
            )
            .await
            .unwrap();

        // Epoch 121 > 110 + 10 grace → expired
        let entry = registry
            .register(
                "test",
                "pyana://b".into(),
                owner_b,
                DelegationAuthority::None,
                121,
                50,
                10,
            )
            .await
            .unwrap();

        assert_eq!(entry.owner, owner_b);
    }

    #[tokio::test]
    async fn cas_version_conflict() {
        let registry = NameRegistry::new();
        let owner = [0x01; 32];

        registry
            .register(
                "myname",
                "pyana://a".into(),
                owner,
                DelegationAuthority::None,
                100,
                50,
                10,
            )
            .await
            .unwrap();

        // Wrong expected version
        let err = registry
            .update("myname", "pyana://b".into(), &owner, 0)
            .await
            .unwrap_err();

        assert!(matches!(err, RegistryError::VersionMismatch { .. }));

        // Correct expected version
        let updated = registry
            .update("myname", "pyana://b".into(), &owner, 1)
            .await
            .unwrap();

        assert_eq!(updated.version, 2);
        assert_eq!(updated.target, "pyana://b");
    }

    #[tokio::test]
    async fn transfer_changes_owner() {
        let registry = NameRegistry::new();
        let owner_a = [0x01; 32];
        let owner_b = [0x02; 32];

        registry
            .register(
                "xname",
                "pyana://a".into(),
                owner_a,
                DelegationAuthority::None,
                100,
                50,
                10,
            )
            .await
            .unwrap();

        let entry = registry.transfer("xname", &owner_a, owner_b).await.unwrap();
        assert_eq!(entry.owner, owner_b);

        // Old owner can no longer update
        let err = registry
            .update("xname", "pyana://c".into(), &owner_a, 2)
            .await
            .unwrap_err();
        assert!(matches!(err, RegistryError::Unauthorized(_)));
    }

    #[tokio::test]
    async fn name_validation() {
        assert!(validate_name("alice").is_ok());
        assert!(validate_name("my-service_01").is_ok());
        assert!(validate_name("").is_err());
        assert!(validate_name("-bad").is_err());
        assert!(validate_name("bad-").is_err());
        assert!(validate_name("BAD").is_err()); // uppercase
        assert!(validate_name("has space").is_err());
    }
}

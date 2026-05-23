//! Sturdy references: swiss number table for durable capability export/enliven/revoke.
//!
//! A swiss number is a 32-byte random secret shared between the holder and the target.
//! Presenting the swiss number to the target's federation proves you were given access.
//! The `SwissTable` maps swiss numbers to capability metadata (cell, permissions, expiry).

use std::collections::HashMap;

use pyana_cell::{AuthRequired, EffectMask};
use pyana_types::CellId;
use serde::{Deserialize, Serialize};

use crate::uri::PyanaUri;

/// Errors that can occur when enlivening a sturdy reference.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EnlivenError {
    /// The swiss number was not found in the table.
    NotFound,
    /// The sturdy reference has expired (past its expiration height).
    Expired,
    /// The sturdy reference has been used the maximum number of times.
    ExhaustedUses,
}

impl std::fmt::Display for EnlivenError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EnlivenError::NotFound => write!(f, "swiss number not found"),
            EnlivenError::Expired => write!(f, "sturdy reference has expired"),
            EnlivenError::ExhaustedUses => {
                write!(f, "sturdy reference exhausted (max uses reached)")
            }
        }
    }
}

impl std::error::Error for EnlivenError {}

/// An entry in the swiss number table, representing an exported sturdy reference.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SwissEntry {
    /// The cell this sturdy reference points to.
    pub cell_id: CellId,
    /// What authorization level the holder obtains upon enlivening.
    pub permissions: AuthRequired,
    /// Optional effect mask restricting which effects the holder can trigger.
    /// `None` means all effects permitted by the cell's own permissions.
    pub allowed_effects: Option<EffectMask>,
    /// Optional expiration expressed as a federation block height.
    /// `None` means the reference never expires.
    pub expires_at: Option<u64>,
    /// Federation height at which this entry was created.
    pub created_at: u64,
    /// Maximum number of times this reference can be enlivened.
    /// `None` means unlimited uses.
    pub max_uses: Option<u32>,
    /// How many times this reference has been enlivened so far.
    pub use_count: u32,
}

/// Swiss number table: maps swiss numbers to capability metadata.
///
/// This is the server-side data structure that a federation node maintains.
/// When a peer presents a swiss number (from a `pyana://` URI), the node
/// looks it up here to determine whether to grant access.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct SwissTable {
    entries: HashMap<[u8; 32], SwissEntry>,
}

impl SwissTable {
    /// Create a new empty swiss table.
    pub fn new() -> Self {
        Self {
            entries: HashMap::new(),
        }
    }

    /// Export a cell as a sturdy reference, generating a new swiss number.
    ///
    /// Returns the generated swiss number. The caller is responsible for
    /// constructing the full `PyanaUri` by combining this with the federation
    /// and cell IDs.
    pub fn export(
        &mut self,
        cell_id: CellId,
        permissions: AuthRequired,
        current_height: u64,
        expires_at: Option<u64>,
    ) -> [u8; 32] {
        let mut swiss = [0u8; 32];
        getrandom::fill(&mut swiss).expect("getrandom failed");
        self.entries.insert(
            swiss,
            SwissEntry {
                cell_id,
                permissions,
                allowed_effects: None,
                expires_at,
                created_at: current_height,
                max_uses: None,
                use_count: 0,
            },
        );
        swiss
    }

    /// Export a cell with full options (effect mask, max uses).
    ///
    /// This is the extended form of `export` that allows specifying an effect mask
    /// and use limit for fine-grained capability attenuation.
    pub fn export_with_options(
        &mut self,
        cell_id: CellId,
        permissions: AuthRequired,
        current_height: u64,
        expires_at: Option<u64>,
        allowed_effects: Option<EffectMask>,
        max_uses: Option<u32>,
    ) -> [u8; 32] {
        let mut swiss = [0u8; 32];
        getrandom::fill(&mut swiss).expect("getrandom failed");
        self.entries.insert(
            swiss,
            SwissEntry {
                cell_id,
                permissions,
                allowed_effects,
                expires_at,
                created_at: current_height,
                max_uses,
                use_count: 0,
            },
        );
        swiss
    }

    /// Construct a full `PyanaUri` for an exported swiss number.
    ///
    /// This is a convenience that combines the swiss number with the federation
    /// and cell IDs to produce the shareable URI.
    pub fn make_uri(&self, federation_id: [u8; 32], swiss: &[u8; 32]) -> Option<PyanaUri> {
        let entry = self.entries.get(swiss)?;
        Some(PyanaUri {
            federation_id,
            cell_id: entry.cell_id.0,
            swiss: *swiss,
        })
    }

    /// Enliven: present a swiss number to get a live capability reference.
    ///
    /// On success, increments the use count and returns the entry metadata.
    /// The caller uses this to create a routing entry for the requester.
    ///
    /// `current_height` is the current federation block height, used for
    /// expiration checks.
    pub fn enliven(
        &mut self,
        swiss: &[u8; 32],
        current_height: u64,
    ) -> Result<SwissEntry, EnlivenError> {
        let entry = self.entries.get_mut(swiss).ok_or(EnlivenError::NotFound)?;

        // Check expiration
        if let Some(exp) = entry.expires_at {
            if current_height > exp {
                return Err(EnlivenError::Expired);
            }
        }

        // Check use limit
        if let Some(max) = entry.max_uses {
            if entry.use_count >= max {
                return Err(EnlivenError::ExhaustedUses);
            }
        }

        entry.use_count += 1;
        Ok(entry.clone())
    }

    /// Revoke a sturdy reference, removing it from the table.
    ///
    /// Returns `true` if the entry existed and was removed, `false` if it
    /// was not found (already revoked or never existed).
    pub fn revoke(&mut self, swiss: &[u8; 32]) -> bool {
        self.entries.remove(swiss).is_some()
    }

    /// Check whether a swiss number exists in the table (without enlivening).
    pub fn contains(&self, swiss: &[u8; 32]) -> bool {
        self.entries.contains_key(swiss)
    }

    /// Get the number of active entries in the table.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Returns true if the table has no entries.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Look up an entry without modifying it (no use-count increment).
    ///
    /// Useful for inspection/diagnostics. Does NOT perform expiration or
    /// use-count checks.
    pub fn peek(&self, swiss: &[u8; 32]) -> Option<&SwissEntry> {
        self.entries.get(swiss)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_cell_id() -> CellId {
        CellId([0xaa; 32])
    }

    #[test]
    fn export_and_enliven() {
        let mut table = SwissTable::new();
        let cell_id = test_cell_id();

        let swiss = table.export(cell_id, AuthRequired::Signature, 100, None);

        // Enliven should succeed
        let entry = table.enliven(&swiss, 100).unwrap();
        assert_eq!(entry.cell_id, cell_id);
        assert_eq!(entry.permissions, AuthRequired::Signature);
        assert_eq!(entry.use_count, 1);
    }

    #[test]
    fn enliven_not_found() {
        let mut table = SwissTable::new();
        let bogus = [0xff; 32];
        let err = table.enliven(&bogus, 100).unwrap_err();
        assert_eq!(err, EnlivenError::NotFound);
    }

    #[test]
    fn enliven_expired() {
        let mut table = SwissTable::new();
        let cell_id = test_cell_id();

        // Expires at height 50
        let swiss = table.export(cell_id, AuthRequired::Signature, 10, Some(50));

        // Current height 51 > expires_at 50
        let err = table.enliven(&swiss, 51).unwrap_err();
        assert_eq!(err, EnlivenError::Expired);

        // Current height 50 == expires_at 50 should still work (not strictly past)
        let entry = table.enliven(&swiss, 50).unwrap();
        assert_eq!(entry.cell_id, cell_id);
    }

    #[test]
    fn enliven_exhausted_uses() {
        let mut table = SwissTable::new();
        let cell_id = test_cell_id();

        // max_uses = 2
        let swiss =
            table.export_with_options(cell_id, AuthRequired::Signature, 10, None, None, Some(2));

        // First use: OK
        let entry = table.enliven(&swiss, 100).unwrap();
        assert_eq!(entry.use_count, 1);

        // Second use: OK
        let entry = table.enliven(&swiss, 101).unwrap();
        assert_eq!(entry.use_count, 2);

        // Third use: exhausted
        let err = table.enliven(&swiss, 102).unwrap_err();
        assert_eq!(err, EnlivenError::ExhaustedUses);
    }

    #[test]
    fn one_time_use() {
        let mut table = SwissTable::new();
        let cell_id = test_cell_id();

        let swiss =
            table.export_with_options(cell_id, AuthRequired::Signature, 10, None, None, Some(1));

        // First enliven succeeds
        table.enliven(&swiss, 100).unwrap();

        // Second enliven fails
        let err = table.enliven(&swiss, 101).unwrap_err();
        assert_eq!(err, EnlivenError::ExhaustedUses);
    }

    #[test]
    fn revoke_then_enliven_fails() {
        let mut table = SwissTable::new();
        let cell_id = test_cell_id();

        let swiss = table.export(cell_id, AuthRequired::Signature, 10, None);

        // Revoke
        assert!(table.revoke(&swiss));
        assert!(!table.revoke(&swiss)); // double revoke returns false

        // Enliven after revoke should fail
        let err = table.enliven(&swiss, 100).unwrap_err();
        assert_eq!(err, EnlivenError::NotFound);
    }

    #[test]
    fn export_uri_format() {
        let mut table = SwissTable::new();
        let cell_id = test_cell_id();
        let federation_id = [0xbb; 32];

        let swiss = table.export(cell_id, AuthRequired::Signature, 10, None);

        let uri = table.make_uri(federation_id, &swiss).unwrap();
        assert_eq!(uri.federation_id, federation_id);
        assert_eq!(uri.cell_id, cell_id.0);
        assert_eq!(uri.swiss, swiss);

        // The URI string should be parseable
        let uri_str = uri.to_uri_string();
        assert!(uri_str.starts_with("pyana://"));
        let parsed = PyanaUri::parse(&uri_str).unwrap();
        assert_eq!(parsed, uri);
    }

    #[test]
    fn contains_and_len() {
        let mut table = SwissTable::new();
        assert!(table.is_empty());

        let swiss = table.export(test_cell_id(), AuthRequired::None, 0, None);
        assert_eq!(table.len(), 1);
        assert!(table.contains(&swiss));
        assert!(!table.contains(&[0xff; 32]));

        table.revoke(&swiss);
        assert!(table.is_empty());
        assert!(!table.contains(&swiss));
    }

    #[test]
    fn effect_mask_attenuation() {
        let mut table = SwissTable::new();
        let cell_id = test_cell_id();

        // Only allow transfer + emit (bits 2 and 4 for example)
        let mask: EffectMask = 0b0001_0100;
        let swiss =
            table.export_with_options(cell_id, AuthRequired::Signature, 10, None, Some(mask), None);

        let entry = table.enliven(&swiss, 100).unwrap();
        assert_eq!(entry.allowed_effects, Some(mask));
    }
}

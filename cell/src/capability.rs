use serde::{Deserialize, Serialize};

use crate::id::CellId;
use crate::permissions::AuthRequired;

/// A reference to a capability — an entry in a cell's c-list.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CapabilityRef {
    /// Which cell this capability points to.
    pub target: CellId,
    /// Local slot number (position in the c-list).
    pub slot: u32,
    /// What authorization is required to exercise this capability.
    pub permissions: AuthRequired,
    /// Optional capability token hash for verification/revocation.
    pub breadstuff: Option<[u8; 32]>,
}

/// The c-list: the set of capabilities a cell holds.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CapabilitySet {
    refs: Vec<CapabilityRef>,
    next_slot: u32,
}

impl CapabilitySet {
    /// Create an empty capability set.
    pub fn new() -> Self {
        CapabilitySet {
            refs: Vec::new(),
            next_slot: 0,
        }
    }

    /// Grant a capability to reach `target` with the given authorization requirement.
    /// Returns the assigned slot number, or `None` if the slot counter would overflow.
    pub fn grant(&mut self, target: CellId, permissions: AuthRequired) -> Option<u32> {
        self.grant_with_breadstuff(target, permissions, None)
    }

    /// Grant a capability with an optional breadstuff token hash.
    /// Returns the assigned slot number, or `None` if the slot counter would overflow.
    pub fn grant_with_breadstuff(
        &mut self,
        target: CellId,
        permissions: AuthRequired,
        breadstuff: Option<[u8; 32]>,
    ) -> Option<u32> {
        let slot = self.next_slot;
        self.next_slot = self.next_slot.checked_add(1)?;
        self.refs.push(CapabilityRef {
            target,
            slot,
            permissions,
            breadstuff,
        });
        Some(slot)
    }

    /// Revoke a capability by slot number. Returns true if found and removed.
    pub fn revoke(&mut self, slot: u32) -> bool {
        let before = self.refs.len();
        self.refs.retain(|r| r.slot != slot);
        self.refs.len() < before
    }

    /// Look up a capability by slot number.
    pub fn lookup(&self, slot: u32) -> Option<&CapabilityRef> {
        self.refs.iter().find(|r| r.slot == slot)
    }

    /// Check if this set contains any non-revoked capability referencing the given target.
    ///
    /// A capability with `permissions: Impossible` is treated as revoked/frozen and
    /// does NOT count as a valid access path.
    pub fn has_access(&self, target: &CellId) -> bool {
        self.refs
            .iter()
            .any(|r| &r.target == target && r.permissions != AuthRequired::Impossible)
    }

    /// Attenuate a capability: create a new CapabilityRef with narrower permissions.
    /// Returns None if the slot doesn't exist or if `narrower` is not actually
    /// narrower than the existing permissions.
    pub fn attenuate(&self, slot: u32, narrower: AuthRequired) -> Option<CapabilityRef> {
        let existing = self.lookup(slot)?;
        // The new permission must be at least as restrictive as the old one.
        if !narrower.is_narrower_or_equal(&existing.permissions) {
            return None;
        }
        Some(CapabilityRef {
            target: existing.target,
            slot: existing.slot,
            permissions: narrower,
            breadstuff: existing.breadstuff,
        })
    }

    /// Restore a previously revoked capability by re-inserting it directly.
    /// Used by journal rollback to undo a revocation.
    pub fn restore(&mut self, cap: CapabilityRef) {
        if !self.refs.iter().any(|r| r.slot == cap.slot) {
            self.refs.push(cap);
        }
    }

    /// Number of active capabilities.
    pub fn len(&self) -> usize {
        self.refs.len()
    }

    /// Whether the capability set is empty.
    pub fn is_empty(&self) -> bool {
        self.refs.is_empty()
    }

    /// Iterate over all capability refs.
    pub fn iter(&self) -> impl Iterator<Item = &CapabilityRef> {
        self.refs.iter()
    }

    /// Get all capabilities targeting a specific cell.
    pub fn capabilities_for(&self, target: &CellId) -> Vec<&CapabilityRef> {
        self.refs.iter().filter(|r| &r.target == target).collect()
    }

    /// Look up the first capability referencing the given target.
    /// Returns None if no capability to that target is held.
    pub fn lookup_by_target(&self, target: &CellId) -> Option<&CapabilityRef> {
        self.refs.iter().find(|r| &r.target == target)
    }
}

impl Default for CapabilitySet {
    fn default() -> Self {
        Self::new()
    }
}

/// Returns true if `granted` permissions are equal to or stricter than `held` permissions.
///
/// This enforces the attenuation-only rule: you can only grant permissions that are
/// as restrictive or more restrictive than what you hold. Never amplification.
pub fn is_attenuation(held: &AuthRequired, granted: &AuthRequired) -> bool {
    granted.is_narrower_or_equal(held)
}

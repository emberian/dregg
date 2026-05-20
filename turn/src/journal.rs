//! LedgerJournal: undo log for efficient atomic rollback.
//!
//! Instead of cloning the entire ledger before executing a turn, the journal
//! records each mutation's previous value as it happens. On success, the journal
//! is simply dropped (zero cost). On failure, the journal is replayed in reverse
//! to restore the ledger to its exact pre-turn state.

use pyana_cell::{
    CapabilityRef, CellId, Ledger, Permissions, VerificationKey,
    state::FieldElement,
};

/// A single undo entry in the journal.
#[derive(Debug)]
pub(crate) enum JournalEntry {
    /// A state field was overwritten. Records the old value.
    SetField {
        cell: CellId,
        index: usize,
        old_value: FieldElement,
    },
    /// A cell's balance was changed (by transfer or fee deduction).
    /// Records the old balance.
    SetBalance {
        cell: CellId,
        old_balance: u64,
    },
    /// A cell's nonce was incremented. Records the old nonce.
    SetNonce {
        cell: CellId,
        old_nonce: u64,
    },
    /// A capability was granted to a cell. Records the slot that was assigned,
    /// so we can revoke it on rollback.
    GrantCapability {
        cell: CellId,
        slot: u32,
    },
    /// A capability was revoked from a cell. Records the full capability
    /// so we can re-grant it on rollback.
    RevokeCapability {
        cell: CellId,
        old_cap: CapabilityRef,
    },
    /// A new cell was created. Records the cell ID so we can remove it on rollback.
    CreateCell {
        cell: CellId,
    },
    /// A cell's proved_state flag was changed. Records the old value.
    SetProvedState {
        cell: CellId,
        old_value: bool,
    },
    /// A cell's permissions were changed. Records the old permissions.
    SetPermissions {
        cell: CellId,
        old_permissions: Permissions,
    },
    /// A cell's verification key was changed. Records the old VK.
    SetVerificationKey {
        cell: CellId,
        old_vk: Option<VerificationKey>,
    },
}

/// The undo journal for a turn's execution.
#[derive(Debug)]
pub(crate) struct LedgerJournal {
    entries: Vec<JournalEntry>,
}

impl LedgerJournal {
    /// Create a new empty journal.
    #[allow(dead_code)]
    pub fn new() -> Self {
        LedgerJournal {
            entries: Vec::new(),
        }
    }

    /// Create a new journal with pre-allocated capacity.
    pub fn with_capacity(cap: usize) -> Self {
        LedgerJournal {
            entries: Vec::with_capacity(cap),
        }
    }

    /// Get a reference to the journal entries for inspection.
    pub fn entries(&self) -> &[JournalEntry] {
        &self.entries
    }

    /// Record a field change.
    pub fn record_set_field(&mut self, cell: CellId, index: usize, old_value: FieldElement) {
        self.entries.push(JournalEntry::SetField { cell, index, old_value });
    }

    /// Record a balance change.
    pub fn record_set_balance(&mut self, cell: CellId, old_balance: u64) {
        self.entries.push(JournalEntry::SetBalance { cell, old_balance });
    }

    /// Record a nonce change.
    pub fn record_set_nonce(&mut self, cell: CellId, old_nonce: u64) {
        self.entries.push(JournalEntry::SetNonce { cell, old_nonce });
    }

    /// Record a capability grant (so it can be revoked on rollback).
    pub fn record_grant_capability(&mut self, cell: CellId, slot: u32) {
        self.entries.push(JournalEntry::GrantCapability { cell, slot });
    }

    /// Record a capability revocation (so it can be re-granted on rollback).
    pub fn record_revoke_capability(&mut self, cell: CellId, old_cap: CapabilityRef) {
        self.entries.push(JournalEntry::RevokeCapability { cell, old_cap });
    }

    /// Record a cell creation (so it can be removed on rollback).
    pub fn record_create_cell(&mut self, cell: CellId) {
        self.entries.push(JournalEntry::CreateCell { cell });
    }

    /// Record a proved_state change.
    pub fn record_set_proved_state(&mut self, cell: CellId, old_value: bool) {
        self.entries.push(JournalEntry::SetProvedState { cell, old_value });
    }

    /// Record a permissions change.
    pub fn record_set_permissions(&mut self, cell: CellId, old_permissions: Permissions) {
        self.entries.push(JournalEntry::SetPermissions { cell, old_permissions });
    }

    /// Record a verification key change.
    pub fn record_set_verification_key(&mut self, cell: CellId, old_vk: Option<VerificationKey>) {
        self.entries.push(JournalEntry::SetVerificationKey { cell, old_vk });
    }

    /// Roll back all recorded changes in reverse order.
    ///
    /// After this call, the ledger is restored to the state it was in before
    /// any journaled mutations were applied.
    pub fn rollback(self, ledger: &mut Ledger) {
        for entry in self.entries.into_iter().rev() {
            match entry {
                JournalEntry::SetField { cell, index, old_value } => {
                    if let Some(c) = ledger.get_mut(&cell) {
                        c.state.fields[index] = old_value;
                    }
                }
                JournalEntry::SetBalance { cell, old_balance } => {
                    if let Some(c) = ledger.get_mut(&cell) {
                        c.state.balance = old_balance;
                    }
                }
                JournalEntry::SetNonce { cell, old_nonce } => {
                    if let Some(c) = ledger.get_mut(&cell) {
                        c.state.nonce = old_nonce;
                    }
                }
                JournalEntry::GrantCapability { cell, slot } => {
                    if let Some(c) = ledger.get_mut(&cell) {
                        c.capabilities.revoke(slot);
                    }
                }
                JournalEntry::RevokeCapability { cell, old_cap } => {
                    if let Some(c) = ledger.get_mut(&cell) {
                        // Re-insert the capability. We use grant_with_breadstuff
                        // but that assigns a new slot. Instead we need to restore
                        // the exact old state. We'll use a direct re-insert.
                        c.capabilities.restore(old_cap);
                    }
                }
                JournalEntry::CreateCell { cell } => {
                    ledger.remove(&cell);
                }
                JournalEntry::SetProvedState { cell, old_value } => {
                    if let Some(c) = ledger.get_mut(&cell) {
                        c.state.proved_state = old_value;
                    }
                }
                JournalEntry::SetPermissions { cell, old_permissions } => {
                    if let Some(c) = ledger.get_mut(&cell) {
                        c.permissions = old_permissions;
                    }
                }
                JournalEntry::SetVerificationKey { cell, old_vk } => {
                    if let Some(c) = ledger.get_mut(&cell) {
                        c.verification_key = old_vk;
                    }
                }
            }
        }
    }
}

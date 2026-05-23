//! LedgerJournal: undo log for efficient atomic rollback.
//!
//! Instead of cloning the entire ledger before executing a turn, the journal
//! records each mutation's previous value as it happens. On success, the journal
//! is simply dropped (zero cost). On failure, the journal is replayed in reverse
//! to restore the ledger to its exact pre-turn state.

use std::collections::HashMap;
use std::sync::Mutex;

use pyana_cell::{
    CapabilityRef, CellId, DelegatedRef, Ledger, NoteCommitment, Nullifier, Permissions,
    VerificationKey, note_bridge::BridgedNullifierSet, state::FieldElement,
};

use crate::action::Symbol;
use crate::escrow::EscrowRecord;
use crate::executor::ObligationRecord;

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
    SetBalance { cell: CellId, old_balance: u64 },
    /// A cell's nonce was incremented. Records the old nonce.
    SetNonce { cell: CellId, old_nonce: u64 },
    /// A capability was granted to a cell. Records the slot that was assigned,
    /// so we can revoke it on rollback.
    GrantCapability { cell: CellId, slot: u32 },
    /// A capability was revoked from a cell. Records the full capability
    /// so we can re-grant it on rollback.
    RevokeCapability {
        cell: CellId,
        old_cap: CapabilityRef,
    },
    /// A new cell was created. Records the cell ID so we can remove it on rollback.
    CreateCell { cell: CellId },
    /// A cell's proved_state flag was changed. Records the old value.
    SetProvedState { cell: CellId, old_value: bool },
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
    /// A cell's delegation was changed. Records the old delegation.
    SetDelegation {
        cell: CellId,
        old_delegation: Option<DelegatedRef>,
    },
    /// A cell's delegation_epoch was changed. Records the old epoch.
    SetDelegationEpoch { cell: CellId, old_epoch: u64 },
    /// A note was spent (nullifier revealed). Recorded so the note layer can
    /// update the nullifier set after the turn commits.
    NoteSpend { nullifier: Nullifier },
    /// A note was created (commitment added). Recorded so the note layer can
    /// insert into the note tree after the turn commits.
    NoteCreate { commitment: NoteCommitment },
    /// An obligation was created. Recorded for the obligation registry.
    ObligationCreated {
        obligor: CellId,
        beneficiary: CellId,
        deadline_height: u64,
        stake: NoteCommitment,
    },
    /// An obligation was fulfilled. Recorded for the obligation registry.
    ObligationFulfilled { obligation_id: [u8; 32] },
    /// An obligation was slashed. Recorded for the obligation registry.
    ObligationSlashed { obligation_id: [u8; 32] },
    /// An event was emitted from a cell. Recorded so the receipt can include it.
    EventEmitted {
        cell: CellId,
        topic: Symbol,
        data: Vec<FieldElement>,
    },
    /// An escrow was created. Recorded for the escrow registry.
    EscrowCreated {
        escrow_id: [u8; 32],
        creator: CellId,
        recipient: CellId,
        amount: u64,
    },
    /// An escrow was released (condition satisfied, funds sent to recipient).
    EscrowReleased { escrow_id: [u8; 32] },
    /// An escrow was refunded (timeout passed, funds returned to creator).
    EscrowRefunded { escrow_id: [u8; 32] },
    /// An obligation was inserted into the executor's obligation map.
    /// On rollback, this obligation_id must be REMOVED from the map.
    ObligationInserted { obligation_id: [u8; 32] },
    /// An escrow was inserted into the executor's escrow map.
    /// On rollback, this escrow_id must be REMOVED from the map.
    EscrowInserted { escrow_id: [u8; 32] },
    /// A bridged nullifier was inserted into the executor's nullifier set.
    /// On rollback, this nullifier must be REMOVED from the set.
    BridgedNullifierInserted { nullifier: [u8; 32] },
    /// A committed escrow was created. Recorded for event tracking.
    CommittedEscrowCreated { escrow_id: [u8; 32], amount: u64 },
    /// A committed escrow was released (recipient claimed).
    CommittedEscrowReleased { escrow_id: [u8; 32] },
    /// A committed escrow was refunded (creator reclaimed after timeout).
    CommittedEscrowRefunded { escrow_id: [u8; 32] },
    /// A committed escrow was inserted into the executor's committed escrow map.
    /// On rollback, this escrow_id must be REMOVED from both committed_escrows
    /// and committed_escrow_amounts maps.
    CommittedEscrowInserted { escrow_id: [u8; 32] },
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
        self.entries.push(JournalEntry::SetField {
            cell,
            index,
            old_value,
        });
    }

    /// Record a balance change.
    pub fn record_set_balance(&mut self, cell: CellId, old_balance: u64) {
        self.entries
            .push(JournalEntry::SetBalance { cell, old_balance });
    }

    /// Record a nonce change.
    pub fn record_set_nonce(&mut self, cell: CellId, old_nonce: u64) {
        self.entries
            .push(JournalEntry::SetNonce { cell, old_nonce });
    }

    /// Record a capability grant (so it can be revoked on rollback).
    pub fn record_grant_capability(&mut self, cell: CellId, slot: u32) {
        self.entries
            .push(JournalEntry::GrantCapability { cell, slot });
    }

    /// Record a capability revocation (so it can be re-granted on rollback).
    pub fn record_revoke_capability(&mut self, cell: CellId, old_cap: CapabilityRef) {
        self.entries
            .push(JournalEntry::RevokeCapability { cell, old_cap });
    }

    /// Record a cell creation (so it can be removed on rollback).
    pub fn record_create_cell(&mut self, cell: CellId) {
        self.entries.push(JournalEntry::CreateCell { cell });
    }

    /// Record a proved_state change.
    pub fn record_set_proved_state(&mut self, cell: CellId, old_value: bool) {
        self.entries
            .push(JournalEntry::SetProvedState { cell, old_value });
    }

    /// Record a permissions change.
    pub fn record_set_permissions(&mut self, cell: CellId, old_permissions: Permissions) {
        self.entries.push(JournalEntry::SetPermissions {
            cell,
            old_permissions,
        });
    }

    /// Record a verification key change.
    pub fn record_set_verification_key(&mut self, cell: CellId, old_vk: Option<VerificationKey>) {
        self.entries
            .push(JournalEntry::SetVerificationKey { cell, old_vk });
    }

    /// Record a delegation change.
    pub fn record_set_delegation(&mut self, cell: CellId, old_delegation: Option<DelegatedRef>) {
        self.entries.push(JournalEntry::SetDelegation {
            cell,
            old_delegation,
        });
    }

    /// Record a delegation_epoch change.
    pub fn record_set_delegation_epoch(&mut self, cell: CellId, old_epoch: u64) {
        self.entries
            .push(JournalEntry::SetDelegationEpoch { cell, old_epoch });
    }

    /// Record a note spend (nullifier revealed).
    pub fn record_note_spend(&mut self, nullifier: Nullifier) {
        self.entries.push(JournalEntry::NoteSpend { nullifier });
    }

    /// Record a note creation (commitment added to tree).
    pub fn record_note_create(&mut self, commitment: NoteCommitment) {
        self.entries.push(JournalEntry::NoteCreate { commitment });
    }

    /// Record an obligation creation.
    pub fn record_obligation_created(
        &mut self,
        obligor: CellId,
        beneficiary: CellId,
        deadline_height: u64,
        stake: NoteCommitment,
    ) {
        self.entries.push(JournalEntry::ObligationCreated {
            obligor,
            beneficiary,
            deadline_height,
            stake,
        });
    }

    /// Record an obligation fulfillment.
    pub fn record_obligation_fulfilled(&mut self, obligation_id: [u8; 32]) {
        self.entries
            .push(JournalEntry::ObligationFulfilled { obligation_id });
    }

    /// Record an obligation slash.
    pub fn record_obligation_slashed(&mut self, obligation_id: [u8; 32]) {
        self.entries
            .push(JournalEntry::ObligationSlashed { obligation_id });
    }

    /// Record an event emission.
    pub fn record_event_emitted(&mut self, cell: CellId, topic: Symbol, data: Vec<FieldElement>) {
        self.entries
            .push(JournalEntry::EventEmitted { cell, topic, data });
    }

    /// Record an escrow creation.
    pub fn record_escrow_created(
        &mut self,
        escrow_id: [u8; 32],
        creator: CellId,
        recipient: CellId,
        amount: u64,
    ) {
        self.entries.push(JournalEntry::EscrowCreated {
            escrow_id,
            creator,
            recipient,
            amount,
        });
    }

    /// Record an escrow release.
    pub fn record_escrow_released(&mut self, escrow_id: [u8; 32]) {
        self.entries
            .push(JournalEntry::EscrowReleased { escrow_id });
    }

    /// Record an escrow refund.
    pub fn record_escrow_refunded(&mut self, escrow_id: [u8; 32]) {
        self.entries
            .push(JournalEntry::EscrowRefunded { escrow_id });
    }

    /// Record that an obligation was inserted into the executor's obligation map.
    /// On rollback, this obligation_id will be removed from the map.
    pub fn record_obligation_inserted(&mut self, obligation_id: [u8; 32]) {
        self.entries
            .push(JournalEntry::ObligationInserted { obligation_id });
    }

    /// Record that an escrow was inserted into the executor's escrow map.
    /// On rollback, this escrow_id will be removed from the map.
    pub fn record_escrow_inserted(&mut self, escrow_id: [u8; 32]) {
        self.entries
            .push(JournalEntry::EscrowInserted { escrow_id });
    }

    /// Record that a bridged nullifier was inserted into the executor's nullifier set.
    /// On rollback, this nullifier will be removed from the set.
    pub fn record_bridged_nullifier_inserted(&mut self, nullifier: [u8; 32]) {
        self.entries
            .push(JournalEntry::BridgedNullifierInserted { nullifier });
    }

    /// Record a committed escrow creation.
    pub fn record_committed_escrow_created(&mut self, escrow_id: [u8; 32], amount: u64) {
        self.entries
            .push(JournalEntry::CommittedEscrowCreated { escrow_id, amount });
    }

    /// Record a committed escrow release.
    pub fn record_committed_escrow_released(&mut self, escrow_id: [u8; 32]) {
        self.entries
            .push(JournalEntry::CommittedEscrowReleased { escrow_id });
    }

    /// Record a committed escrow refund.
    pub fn record_committed_escrow_refunded(&mut self, escrow_id: [u8; 32]) {
        self.entries
            .push(JournalEntry::CommittedEscrowRefunded { escrow_id });
    }

    /// Record that a committed escrow was inserted into the executor's maps.
    /// On rollback, this escrow_id will be removed from both committed_escrows
    /// and committed_escrow_amounts.
    pub fn record_committed_escrow_inserted(&mut self, escrow_id: [u8; 32]) {
        self.entries
            .push(JournalEntry::CommittedEscrowInserted { escrow_id });
    }

    /// Roll back all recorded changes in reverse order.
    ///
    /// After this call, the ledger is restored to the state it was in before
    /// any journaled mutations were applied. Also removes any obligation/escrow/
    /// nullifier insertions that were recorded during the turn from the executor's
    /// in-memory maps, preventing phantom record attacks.
    pub fn rollback(
        self,
        ledger: &mut Ledger,
        obligations: &Mutex<HashMap<[u8; 32], ObligationRecord>>,
        escrows: &Mutex<HashMap<[u8; 32], EscrowRecord>>,
        bridged_nullifiers: &Mutex<BridgedNullifierSet>,
        committed_escrows: &Mutex<HashMap<[u8; 32], crate::escrow::CommittedEscrow>>,
        committed_escrow_amounts: &Mutex<HashMap<[u8; 32], u64>>,
    ) {
        for entry in self.entries.into_iter().rev() {
            match entry {
                JournalEntry::SetField {
                    cell,
                    index,
                    old_value,
                } => {
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
                JournalEntry::SetPermissions {
                    cell,
                    old_permissions,
                } => {
                    if let Some(c) = ledger.get_mut(&cell) {
                        c.permissions = old_permissions;
                    }
                }
                JournalEntry::SetVerificationKey { cell, old_vk } => {
                    if let Some(c) = ledger.get_mut(&cell) {
                        c.verification_key = old_vk;
                    }
                }
                JournalEntry::SetDelegation {
                    cell,
                    old_delegation,
                } => {
                    if let Some(c) = ledger.get_mut(&cell) {
                        c.delegation = old_delegation;
                    }
                }
                JournalEntry::SetDelegationEpoch { cell, old_epoch } => {
                    if let Some(c) = ledger.get_mut(&cell) {
                        c.state.delegation_epoch = old_epoch;
                    }
                }
                // CRITICAL FIX: Remove obligation/escrow/nullifier insertions on rollback.
                // Without this, an attacker could create phantom records that survive
                // a failed turn and exploit them in subsequent turns for inflation.
                JournalEntry::ObligationInserted { obligation_id } => {
                    obligations.lock().unwrap().remove(&obligation_id);
                }
                JournalEntry::EscrowInserted { escrow_id } => {
                    escrows.lock().unwrap().remove(&escrow_id);
                }
                JournalEntry::BridgedNullifierInserted { nullifier } => {
                    bridged_nullifiers.lock().unwrap().remove(&nullifier);
                }
                JournalEntry::CommittedEscrowInserted { escrow_id } => {
                    committed_escrows.lock().unwrap().remove(&escrow_id);
                    committed_escrow_amounts.lock().unwrap().remove(&escrow_id);
                }
                // Note/obligation/escrow/event entries don't modify ledger state directly.
                // On rollback these are simply discarded — the note layer,
                // obligation registry, and escrow registry only process them after
                // a successful commit.
                JournalEntry::NoteSpend { .. }
                | JournalEntry::NoteCreate { .. }
                | JournalEntry::ObligationCreated { .. }
                | JournalEntry::ObligationFulfilled { .. }
                | JournalEntry::ObligationSlashed { .. }
                | JournalEntry::EscrowCreated { .. }
                | JournalEntry::EscrowReleased { .. }
                | JournalEntry::EscrowRefunded { .. }
                | JournalEntry::CommittedEscrowCreated { .. }
                | JournalEntry::CommittedEscrowReleased { .. }
                | JournalEntry::CommittedEscrowRefunded { .. }
                | JournalEntry::EventEmitted { .. } => {}
            }
        }
    }
}

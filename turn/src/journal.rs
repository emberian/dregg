//! LedgerJournal: undo log for efficient atomic rollback.
//!
//! Instead of cloning the entire ledger before executing a turn, the journal
//! records each mutation's previous value as it happens. On success, the journal
//! is simply dropped (zero cost). On failure, the journal is replayed in reverse
//! to restore the ledger to its exact pre-turn state.

use std::sync::Mutex;

use dregg_cell::{
    CapabilityRef, CellId, CellProgram, DelegatedRef, Ledger, NoteCommitment, Nullifier,
    Permissions, VerificationKey,
    lifecycle::CellLifecycle,
    nullifier_set::NullifierSet,
    permissions::AuthRequired,
    state::{FieldElement, STATE_SLOTS},
};

use crate::action::Symbol;
use dregg_cell_crypto::note_bridge::BridgedNullifierSet;

/// A single undo entry in the journal.
#[derive(Debug)]
pub(crate) enum JournalEntry {
    /// A state field was overwritten. Records the old value (`None` for a heap
    /// key that was absent before this turn — the universal-map absent leg).
    SetField {
        cell: CellId,
        index: usize,
        old_value: Option<FieldElement>,
    },
    /// A cell's balance was changed (by transfer or fee deduction).
    /// Records the old balance. SIGNED (THE EPOCH §5): a well's prior
    /// balance may be negative.
    SetBalance { cell: CellId, old_balance: i64 },
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
    /// A cell's program (caveat table) was changed. Records the old program
    /// so a rejected turn restores it (atomic reversibility).
    SetProgram {
        cell: CellId,
        old_program: CellProgram,
    },
    /// A cell's delegation was changed. Records the old delegation.
    SetDelegation {
        cell: CellId,
        old_delegation: Option<DelegatedRef>,
    },
    /// A cell's delegation_epoch was changed. Records the old epoch.
    SetDelegationEpoch { cell: CellId, old_epoch: u64 },
    /// A cell's committed_height was changed. Records the old height.
    SetCommittedHeight { cell: CellId, old_height: u64 },
    /// A note was spent (nullifier revealed). Marker for journal replay ordering;
    /// actual nullifier insertion is tracked via NoteNullifierInserted.
    NoteSpend,
    /// A note was created (commitment added). Marker for journal replay ordering.
    NoteCreate,
    /// An event was emitted from a cell. Recorded so the receipt can include it.
    EventEmitted {
        cell: CellId,
        topic: Symbol,
        data: Vec<FieldElement>,
    },
    /// A bridged nullifier was inserted into the executor's nullifier set.
    /// On rollback, this nullifier must be REMOVED from the set.
    BridgedNullifierInserted { nullifier: [u8; 32] },
    /// A note-spend nullifier was inserted into the executor's production
    /// `note_nullifiers` set. On rollback this nullifier must be REMOVED so
    /// a failed turn doesn't permanently burn the note.
    NoteNullifierInserted { nullifier: Nullifier },
    /// A cell's lifecycle state was changed (Seal, Unseal, Destroy, Archive).
    /// Records the old lifecycle so rollback can restore it.
    SetLifecycle {
        cell: CellId,
        old_lifecycle: CellLifecycle,
    },
    /// A cell's heap entry `(collection, key)` was written (the openable
    /// sorted-Poseidon2 `(collection, key) → value` heap whose committed root is
    /// `CellState.heap_root`). Records the old value (`None` for a key that was
    /// absent before this turn — the universal-memory absent leg, exactly like
    /// `SetField`). On rollback the prior value is restored (or the key removed)
    /// and the heap root re-sealed. The umem bridge re-reads this as the heap
    /// domain's Blum write — see [`crate::umem::UKey::Heap`].
    ///
    /// NAMED SEAM (UMEM-PRIMITIVE §2, Stage A): the rollback + bridge wiring is
    /// complete and exercised by `turn/tests/umem_heap.rs`, but no live `Effect`
    /// journals a heap write yet — today the heap is mutated out-of-band
    /// (`CellState::set_heap`, e.g. `deos-js`/`dregg-doc`). The producer is a
    /// heap-writing effect, a new effect/circuit surface (Stage B+) deliberately
    /// NOT built here. `#[allow(dead_code)]` until that producer lands.
    #[allow(dead_code)]
    SetHeap {
        cell: CellId,
        collection: u32,
        key: u32,
        old_value: Option<FieldElement>,
    },
    /// A capability slot was attenuated in place. Records the prior values
    /// of the three narrow-able fields (permissions, allowed_effects, expires_at)
    /// so rollback can restore the slot exactly.
    AttenuateCapability {
        cell: CellId,
        slot: u32,
        old_permissions: AuthRequired,
        old_allowed_effects: Option<dregg_cell::EffectMask>,
        old_expires_at: Option<u64>,
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

    /// **The exact write-set** — every cell whose serialized state this turn
    /// mutated, distinct, in first-touch order. Because the journal records one
    /// entry per mutation and each entry names the cell it changed, this set is
    /// COMPLETE by construction — unlike a syntactic effect walk over the input
    /// turn, which must re-derive (and can miss) the cells an effect resolves at
    /// runtime (a burn's issuer well, a create's newborn id, a factory birth,
    /// the metered agent). Consumers that must reconstruct post-state from a
    /// per-turn change-set (the durable commit-log overlay — see CORE-AUDIT.md
    /// finding 1) MUST use this, not `touched_cells(&turn)`.
    ///
    /// A cell that appears without a net state change is a harmless
    /// over-approximation (its recorded post-state reconstructs identically); a
    /// MISSING cell is the soundness bug this closes. The nullifier-set markers
    /// (`NoteSpend`/`NoteCreate`/`*NullifierInserted`) carry no cell — they mutate
    /// executor-side sets, not cell state — and are excluded.
    pub fn touched_cells(&self) -> Vec<CellId> {
        let mut out: Vec<CellId> = Vec::new();
        for entry in &self.entries {
            let cell = match entry {
                JournalEntry::SetField { cell, .. }
                | JournalEntry::SetBalance { cell, .. }
                | JournalEntry::SetNonce { cell, .. }
                | JournalEntry::GrantCapability { cell, .. }
                | JournalEntry::RevokeCapability { cell, .. }
                | JournalEntry::CreateCell { cell }
                | JournalEntry::SetProvedState { cell, .. }
                | JournalEntry::SetPermissions { cell, .. }
                | JournalEntry::SetVerificationKey { cell, .. }
                | JournalEntry::SetProgram { cell, .. }
                | JournalEntry::SetDelegation { cell, .. }
                | JournalEntry::SetDelegationEpoch { cell, .. }
                | JournalEntry::SetCommittedHeight { cell, .. }
                | JournalEntry::EventEmitted { cell, .. }
                | JournalEntry::SetLifecycle { cell, .. }
                | JournalEntry::SetHeap { cell, .. }
                | JournalEntry::AttenuateCapability { cell, .. } => *cell,
                JournalEntry::NoteSpend
                | JournalEntry::NoteCreate
                | JournalEntry::BridgedNullifierInserted { .. }
                | JournalEntry::NoteNullifierInserted { .. } => continue,
            };
            if !out.contains(&cell) {
                out.push(cell);
            }
        }
        out
    }

    /// Record a field change. `old_value = None` means the heap key was absent
    /// before this turn; fixed slots are always `Some`.
    pub fn record_set_field(
        &mut self,
        cell: CellId,
        index: usize,
        old_value: Option<FieldElement>,
    ) {
        self.entries.push(JournalEntry::SetField {
            cell,
            index,
            old_value,
        });
    }

    /// Record a balance change.
    pub fn record_set_balance(&mut self, cell: CellId, old_balance: i64) {
        self.entries
            .push(JournalEntry::SetBalance { cell, old_balance });
    }

    /// Record a nonce change.
    pub fn record_set_nonce(&mut self, cell: CellId, old_nonce: u64) {
        self.entries
            .push(JournalEntry::SetNonce { cell, old_nonce });
    }

    /// Record a heap write. `old_value = None` means the `(collection, key)`
    /// was absent before this turn. (Awaiting the live heap-writing effect
    /// producer — see [`JournalEntry::SetHeap`]'s NAMED SEAM note.)
    #[allow(dead_code)]
    pub fn record_set_heap(
        &mut self,
        cell: CellId,
        collection: u32,
        key: u32,
        old_value: Option<FieldElement>,
    ) {
        self.entries.push(JournalEntry::SetHeap {
            cell,
            collection,
            key,
            old_value,
        });
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

    /// Record a program (caveat table) change.
    pub fn record_set_program(&mut self, cell: CellId, old_program: CellProgram) {
        self.entries
            .push(JournalEntry::SetProgram { cell, old_program });
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

    /// Record a committed_height change.
    pub fn record_set_committed_height(&mut self, cell: CellId, old_height: u64) {
        self.entries
            .push(JournalEntry::SetCommittedHeight { cell, old_height });
    }

    /// Record a note spend (nullifier revealed). Actual nullifier insertion
    /// is tracked separately via `record_note_nullifier_inserted`.
    pub fn record_note_spend(&mut self, _nullifier: Nullifier) {
        self.entries.push(JournalEntry::NoteSpend);
    }

    /// Record a note creation (commitment added to tree). Ordering marker only.
    pub fn record_note_create(&mut self, _commitment: NoteCommitment) {
        self.entries.push(JournalEntry::NoteCreate);
    }

    /// Record an event emission.
    pub fn record_event_emitted(&mut self, cell: CellId, topic: Symbol, data: Vec<FieldElement>) {
        self.entries
            .push(JournalEntry::EventEmitted { cell, topic, data });
    }

    /// Record that a bridged nullifier was inserted into the executor's nullifier set.
    /// On rollback, this nullifier will be removed from the set.
    pub fn record_bridged_nullifier_inserted(&mut self, nullifier: [u8; 32]) {
        self.entries
            .push(JournalEntry::BridgedNullifierInserted { nullifier });
    }

    /// Record that a note-spend nullifier was inserted into the executor's
    /// production `note_nullifiers` set. On rollback, this nullifier will be
    /// removed so a failed turn doesn't permanently burn the note.
    pub fn record_note_nullifier_inserted(&mut self, nullifier: Nullifier) {
        self.entries
            .push(JournalEntry::NoteNullifierInserted { nullifier });
    }

    /// Record a cell-lifecycle change (Seal/Unseal/Destroy/Archive).
    pub fn record_set_lifecycle(&mut self, cell: CellId, old_lifecycle: CellLifecycle) {
        self.entries.push(JournalEntry::SetLifecycle {
            cell,
            old_lifecycle,
        });
    }

    /// Record an in-place capability attenuation.
    pub fn record_attenuate_capability(
        &mut self,
        cell: CellId,
        slot: u32,
        old_permissions: AuthRequired,
        old_allowed_effects: Option<dregg_cell::EffectMask>,
        old_expires_at: Option<u64>,
    ) {
        self.entries.push(JournalEntry::AttenuateCapability {
            cell,
            slot,
            old_permissions,
            old_allowed_effects,
            old_expires_at,
        });
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
        bridged_nullifiers: &Mutex<BridgedNullifierSet>,
        note_nullifiers: &Mutex<NullifierSet>,
    ) {
        for entry in self.entries.into_iter().rev() {
            match entry {
                JournalEntry::SetField {
                    cell,
                    index,
                    old_value,
                } => {
                    if let Some(c) = ledger.get_mut(&cell) {
                        if index < STATE_SLOTS {
                            c.state.fields[index] = old_value.expect(
                                "fixed-slot SetField rollback always carries the prior value",
                            );
                        } else if let Some(v) = old_value {
                            c.state.set_field_ext(index as u64, v);
                        } else {
                            c.state.fields_map.remove(&(index as u64));
                            c.state.reseal_fields_root();
                        }
                    }
                }
                JournalEntry::SetBalance { cell, old_balance } => {
                    if let Some(c) = ledger.get_mut(&cell) {
                        c.state.set_balance(old_balance);
                    }
                }
                JournalEntry::SetNonce { cell, old_nonce } => {
                    if let Some(c) = ledger.get_mut(&cell) {
                        c.state.set_nonce(old_nonce);
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
                        c.state.set_proved_state(old_value);
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
                JournalEntry::SetProgram { cell, old_program } => {
                    if let Some(c) = ledger.get_mut(&cell) {
                        c.program = old_program;
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
                        c.state.set_delegation_epoch(old_epoch);
                    }
                }
                JournalEntry::SetCommittedHeight { cell, old_height } => {
                    if let Some(c) = ledger.get_mut(&cell) {
                        c.state.set_committed_height(old_height);
                    }
                }
                // CRITICAL FIX: Remove nullifier insertions on rollback.
                // Without this, an attacker could create phantom records that survive
                // a failed turn and exploit them in subsequent turns for inflation.
                JournalEntry::BridgedNullifierInserted { nullifier } => {
                    bridged_nullifiers.lock().unwrap().remove(&nullifier);
                }
                JournalEntry::NoteNullifierInserted { nullifier } => {
                    note_nullifiers.lock().unwrap().remove(&nullifier);
                }
                JournalEntry::SetLifecycle {
                    cell,
                    old_lifecycle,
                } => {
                    if let Some(c) = ledger.get_mut(&cell) {
                        c.lifecycle = old_lifecycle;
                    }
                }
                JournalEntry::SetHeap {
                    cell,
                    collection,
                    key,
                    old_value,
                } => {
                    if let Some(c) = ledger.get_mut(&cell) {
                        match old_value {
                            Some(v) => {
                                c.state.set_heap(collection, key, v);
                            }
                            None => {
                                c.state.remove_heap(collection, key);
                            }
                        }
                    }
                }
                JournalEntry::AttenuateCapability {
                    cell,
                    slot,
                    old_permissions,
                    old_allowed_effects,
                    old_expires_at,
                } => {
                    if let Some(c) = ledger.get_mut(&cell) {
                        // Directly restore the slot's fields via a
                        // mutable lookup (CapabilitySet exposes
                        // attenuate_in_place, but rollback may need to
                        // widen back to the original — bypass the
                        // narrowing check by mutating in place).
                        if let Some(cap) = c.capabilities.iter_mut().find(|r| r.slot == slot) {
                            cap.permissions = old_permissions;
                            cap.allowed_effects = old_allowed_effects;
                            cap.expires_at = old_expires_at;
                        }
                    }
                }
                // Note/event entries don't modify ledger state directly.
                // On rollback these are simply discarded — the note layer only
                // processes them after a successful commit.
                JournalEntry::NoteSpend
                | JournalEntry::NoteCreate
                | JournalEntry::EventEmitted { .. } => {}
            }
        }
    }
}

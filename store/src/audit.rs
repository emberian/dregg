//! Audit log persistent storage.
//!
//! Stores audit events in a strictly ordered append-only log, indexed by
//! sequence number. A secondary index enables efficient lookup of all events
//! for a specific token.
//!
//! Each event gets a globally unique, monotonically increasing sequence number.
//! The sequence counter is persisted in the metadata table so it survives restarts.

use redb::ReadableTable;
use serde::{Deserialize, Serialize};

use crate::tables;
use crate::{PersistentStore, Result, StoreError};

/// A stored audit event, representing a single token usage or action.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct StoredAuditEvent {
    /// The token ID this event pertains to (32 bytes).
    pub token_id: [u8; 32],
    /// The type of event.
    pub event_type: AuditEventType,
    /// Unix timestamp (seconds) when the event occurred.
    pub timestamp: i64,
    /// Hash of the action or context (opaque 32 bytes).
    pub action_hash: [u8; 32],
    /// The actor that triggered the event (e.g., verifier ID).
    pub actor: [u8; 32],
    /// The global sequence number (assigned on append).
    pub sequence: u64,
    /// Optional additional data (e.g., serialized details).
    pub metadata: Vec<u8>,
}

/// Types of audit events that can be recorded.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum AuditEventType {
    /// Token was presented for authorization.
    TokenPresented,
    /// Token was attenuated (a fold step was applied).
    TokenAttenuated,
    /// Token was revoked.
    TokenRevoked,
    /// Token was issued (initial creation).
    TokenIssued,
    /// A key operation (rotation, creation, etc.).
    KeyOperation,
    /// Federation consensus event.
    ConsensusEvent,
    /// Generic/custom event.
    Custom(String),
}

impl PersistentStore {
    /// Append an audit event to the log.
    ///
    /// Assigns the next sequence number and stores the event. Also updates
    /// the token index for efficient per-token queries.
    ///
    /// Returns the assigned sequence number.
    pub fn append_audit_event(&self, event: &StoredAuditEvent) -> Result<u64> {
        let write_txn = self.db.begin_write()?;
        let sequence = {
            // Get and increment the sequence counter.
            let mut meta = write_txn.open_table(tables::METADATA)?;
            let next_seq = meta
                .get(tables::META_AUDIT_NEXT_SEQ)?
                .map(|g| g.value())
                .unwrap_or(0);

            // Store the event with the assigned sequence.
            let mut stored = event.clone();
            stored.sequence = next_seq;
            let serialized = postcard::to_stdvec(&stored)?;

            let mut log_table = write_txn.open_table(tables::AUDIT_LOG)?;
            log_table.insert(next_seq, serialized.as_slice())?;

            // Update the token index.
            let mut idx_table = write_txn.open_table(tables::AUDIT_TOKEN_INDEX)?;
            let index_key = make_token_index_key(&stored.token_id, next_seq);
            idx_table.insert(index_key.as_str(), next_seq)?;

            // Increment the counter.
            meta.insert(tables::META_AUDIT_NEXT_SEQ, next_seq + 1)?;

            next_seq
        };
        write_txn.commit()?;
        Ok(sequence)
    }

    /// Get an audit event by its sequence number.
    pub fn get_audit_event(&self, sequence: u64) -> Result<Option<StoredAuditEvent>> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::AUDIT_LOG)?;

        match table.get(sequence)? {
            Some(value) => {
                let event: StoredAuditEvent = postcard::from_bytes(value.value())?;
                Ok(Some(event))
            }
            None => Ok(None),
        }
    }

    /// Get the total number of audit events.
    pub fn audit_count(&self) -> Result<u64> {
        let read_txn = self.db.begin_read()?;
        let meta = read_txn.open_table(tables::METADATA)?;
        Ok(meta
            .get(tables::META_AUDIT_NEXT_SEQ)?
            .map(|g| g.value())
            .unwrap_or(0))
    }

    /// Get all audit events for a specific token ID.
    ///
    /// Uses the secondary index for efficient lookup.
    pub fn audit_events_for_token(&self, token_id: &[u8; 32]) -> Result<Vec<StoredAuditEvent>> {
        let read_txn = self.db.begin_read()?;
        let idx_table = read_txn.open_table(tables::AUDIT_TOKEN_INDEX)?;
        let log_table = read_txn.open_table(tables::AUDIT_LOG)?;

        let prefix = token_id_hex(token_id);
        let range_start = format!("{prefix}:");
        let range_end = format!("{prefix};"); // ';' is one past ':' in ASCII.

        let range = idx_table.range(range_start.as_str()..range_end.as_str())?;
        let mut events = Vec::new();

        for entry in range {
            let entry =
                entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
            let seq = entry.1.value();

            if let Some(value) = log_table.get(seq)? {
                let event: StoredAuditEvent = postcard::from_bytes(value.value())?;
                events.push(event);
            }
        }

        Ok(events)
    }

    /// Get audit events in a sequence range (inclusive start, exclusive end).
    pub fn audit_events_range(&self, start: u64, end: u64) -> Result<Vec<StoredAuditEvent>> {
        let read_txn = self.db.begin_read()?;
        let table = read_txn.open_table(tables::AUDIT_LOG)?;

        let range = table.range(start..end)?;
        let mut events = Vec::new();

        for entry in range {
            let entry =
                entry.map_err(|e: redb::StorageError| StoreError::Database(e.to_string()))?;
            let event: StoredAuditEvent = postcard::from_bytes(entry.1.value())?;
            events.push(event);
        }

        Ok(events)
    }

    /// Get the latest N audit events (most recent first).
    pub fn latest_audit_events(&self, count: u64) -> Result<Vec<StoredAuditEvent>> {
        let total = self.audit_count()?;
        if total == 0 {
            return Ok(Vec::new());
        }

        let start = total.saturating_sub(count);
        let mut events = self.audit_events_range(start, total)?;
        events.reverse();
        Ok(events)
    }

    /// Append multiple audit events in a single transaction.
    ///
    /// Returns the sequence number of the first event in the batch.
    pub fn append_audit_events_batch(&self, events: &[StoredAuditEvent]) -> Result<u64> {
        if events.is_empty() {
            return self.audit_count();
        }

        let write_txn = self.db.begin_write()?;
        let first_seq = {
            let mut meta = write_txn.open_table(tables::METADATA)?;
            let mut next_seq = meta
                .get(tables::META_AUDIT_NEXT_SEQ)?
                .map(|g| g.value())
                .unwrap_or(0);
            let first = next_seq;

            let mut log_table = write_txn.open_table(tables::AUDIT_LOG)?;
            let mut idx_table = write_txn.open_table(tables::AUDIT_TOKEN_INDEX)?;

            for event in events {
                let mut stored = event.clone();
                stored.sequence = next_seq;
                let serialized = postcard::to_stdvec(&stored)?;

                log_table.insert(next_seq, serialized.as_slice())?;

                let index_key = make_token_index_key(&stored.token_id, next_seq);
                idx_table.insert(index_key.as_str(), next_seq)?;

                next_seq += 1;
            }

            meta.insert(tables::META_AUDIT_NEXT_SEQ, next_seq)?;
            first
        };
        write_txn.commit()?;
        Ok(first_seq)
    }
}

// =============================================================================
// Audit Log Bridge (pyana-audit <-> pyana-store)
// =============================================================================

/// Bridge between the in-memory `pyana-audit` `AuditLog` (with Merkle proofs)
/// and the persistent `pyana-store` audit storage.
///
/// The in-memory `AuditLog` is the **canonical** audit system: it maintains a
/// 4-ary Merkle tree over events and can produce inclusion proofs, count proofs,
/// range proofs, and consistency proofs. The persistent store provides durability
/// across restarts.
///
/// Use [`PersistentStore::persist_audit_events`] to flush in-memory events to disk.
///
/// # Deprecation of standalone persistent audit
///
/// The standalone `append_audit_event` / `audit_events_for_token` methods on
/// `PersistentStore` remain available for backward compatibility, but new code
/// should use the in-memory `AuditLog` as the primary system and call
/// `persist_audit_events` periodically to durably store events.
#[cfg(feature = "audit-bridge")]
impl PersistentStore {
    /// Persist events from an in-memory `AuditLog` to durable storage.
    ///
    /// Converts each `UsageEvent` in the range `[from_index, to_index)` to a
    /// `StoredAuditEvent` and appends them in a single batch transaction.
    ///
    /// Returns the number of events persisted.
    pub fn persist_audit_events(
        &self,
        log: &pyana_audit::AuditLog,
        from_index: u64,
        to_index: u64,
    ) -> Result<u64> {
        let mut batch = Vec::new();
        for idx in from_index..to_index {
            let event = log
                .get_event(idx)
                .ok_or_else(|| StoreError::NotFound)?;
            batch.push(StoredAuditEvent {
                token_id: event.token_id,
                event_type: AuditEventType::TokenPresented,
                timestamp: event.timestamp,
                action_hash: event.action_hash,
                actor: event.verifier_id,
                sequence: event.sequence,
                metadata: Vec::new(),
            });
        }

        if batch.is_empty() {
            return Ok(0);
        }

        self.append_audit_events_batch(&batch)?;
        Ok(batch.len() as u64)
    }

    /// Persist ALL events from an in-memory `AuditLog` that haven't been
    /// persisted yet (based on comparing sizes).
    ///
    /// Returns the number of newly persisted events.
    pub fn persist_audit_log(&self, log: &pyana_audit::AuditLog) -> Result<u64> {
        let persisted_count = self.audit_count()?;
        let log_size = log.len() as u64;

        if log_size <= persisted_count {
            return Ok(0);
        }

        self.persist_audit_events(log, persisted_count, log_size)
    }
}

// =============================================================================
// Helpers
// =============================================================================

/// Create the index key for the token index table.
/// Format: "{hex(token_id)}:{sequence:020}" (zero-padded for correct sort order).
fn make_token_index_key(token_id: &[u8; 32], sequence: u64) -> String {
    format!("{}:{sequence:020}", token_id_hex(token_id))
}

/// Convert a token ID to its hex string representation.
fn token_id_hex(token_id: &[u8; 32]) -> String {
    token_id.iter().map(|b| format!("{b:02x}")).collect()
}

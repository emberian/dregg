//! Metered store-and-forward relay.
//!
//! # DEPRECATED — folds into `pyana_storage_templates::relay_operator`
//!
//! Per `STORAGE-AS-CELL-PROGRAMS.md` §3.5 + §6.1 this module's
//! [`MeteredRelay`] / [`MeteredMessage`] surface folds into the
//! relay-operator cell's `relay` action: the metering becomes the
//! template's `RateLimitBySum` constraint on
//! `bytes_relayed_this_epoch`; the per-destination Merkle queues
//! become individual `CapInboxTemplate` cells registered through the
//! relay's `register_inbox` action. The underlying [`MerkleQueue`]
//! data structure stays.
//!
//! Wraps the captp store-and-forward concept with resource accounting.
//! Every message buffered for an offline destination costs computrons.
//! The relay node is providing a SERVICE (storage + eventual delivery).
//! If the sender's quota is exhausted, messages are rejected.
//! TTL-based pricing: longer TTL = more expensive (rent model).
//!
//! Phase 4: MerkleQueue backend. Each destination gets a provable queue.
//! Queue roots are content-addressed and verifiable.

#![allow(deprecated)]

use std::collections::HashMap;

use crate::queue::{DequeueProof, MerkleQueue, QueueEntry, QueueError};
use crate::quota::SpaceBank;
use crate::{ComputronRefund, QuotaId, StorageError};

/// A message buffered in the relay with metering metadata.
#[derive(Debug, Clone)]
pub struct MeteredMessage {
    /// Destination node (public key).
    pub destination: [u8; 32],
    /// Message payload.
    pub payload: Vec<u8>,
    /// Block height when this message was enqueued.
    pub enqueued_at: u64,
    /// Time-to-live in blocks. After enqueued_at + ttl_blocks, message expires.
    pub ttl_blocks: u64,
    /// Quota cell that paid for buffering.
    pub payer: QuotaId,
    /// Computrons charged for this message.
    pub cost_paid: u64,
}

/// Error from relay operations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RelayError {
    /// Sender's quota is exhausted.
    QuotaExhausted { available: u64, required: u64 },
    /// Quota cell not found.
    QuotaNotFound(QuotaId),
    /// Message too large.
    MessageTooLarge { size: usize, max: usize },
    /// Invalid TTL.
    InvalidTtl,
    /// Queue is full for this destination.
    QueueFull { capacity: usize },
    /// Destination inbox not found.
    InboxNotFound { destination: [u8; 32] },
    /// Operator is underbonded (cannot accept new inboxes).
    Underbonded { required: u64, actual: u64 },
    /// Inbox already hosted.
    AlreadyHosted { owner: [u8; 32] },
    /// Insufficient deposit.
    InsufficientDeposit { provided: u64, minimum: u64 },
}

impl From<StorageError> for RelayError {
    fn from(e: StorageError) -> Self {
        match e {
            StorageError::QuotaExhausted {
                available,
                required,
            } => RelayError::QuotaExhausted {
                available,
                required,
            },
            StorageError::QuotaNotFound(id) => RelayError::QuotaNotFound(id),
            _ => RelayError::QuotaExhausted {
                available: 0,
                required: 0,
            },
        }
    }
}

impl From<QueueError> for RelayError {
    fn from(e: QueueError) -> Self {
        match e {
            QueueError::Full { capacity } => RelayError::QueueFull { capacity },
            QueueError::Empty => RelayError::QueueFull { capacity: 0 },
        }
    }
}

/// Metered store-and-forward relay node.
///
/// Phase 4 refactor: uses MerkleQueue per destination instead of VecDeque.
/// Queue roots are content-addressed and verifiable.
#[deprecated(
    since = "0.1.0",
    note = "Folds into `pyana_storage_templates::relay_operator` per STORAGE-AS-CELL-PROGRAMS.md §3.5 + §6.1. Per-destination metering becomes the relay-operator cell's `RateLimitBySum` constraint on `bytes_relayed_this_epoch`."
)]
#[derive(Debug)]
pub struct MeteredRelay {
    /// Per-destination Merkle queues (content-addressed, provable).
    queues: HashMap<[u8; 32], MerkleQueue>,
    /// Message metadata indexed by (destination, position) for TTL/refund tracking.
    metadata: HashMap<[u8; 32], Vec<MessageMeta>>,
    /// The space bank governing quota for relay operations.
    pub bank: SpaceBank,
    /// Maximum message size in bytes.
    pub max_message_size: usize,
    /// Maximum TTL in blocks.
    pub max_ttl: u64,
    /// Current block height (for expiry).
    pub current_block: u64,
    /// Default queue capacity per destination.
    pub default_queue_capacity: usize,
}

/// Metadata tracked per message for TTL/refund purposes.
#[derive(Debug, Clone)]
struct MessageMeta {
    pub enqueued_at: u64,
    pub ttl_blocks: u64,
    pub payer: QuotaId,
    pub cost_paid: u64,
    pub size: usize,
}

impl MeteredRelay {
    /// Create a new metered relay with the given space bank.
    pub fn new(bank: SpaceBank, max_message_size: usize, max_ttl: u64) -> Self {
        Self {
            queues: HashMap::new(),
            metadata: HashMap::new(),
            bank,
            max_message_size,
            max_ttl,
            current_block: 0,
            default_queue_capacity: 1000,
        }
    }

    /// Enqueue a message for buffered delivery.
    /// Charges the payer's quota based on message size and TTL.
    /// Returns the new queue root hash on success.
    pub fn enqueue(
        &mut self,
        destination: [u8; 32],
        payload: Vec<u8>,
        ttl_blocks: u64,
        payer: &QuotaId,
    ) -> Result<[u8; 32], RelayError> {
        // Validate.
        if payload.len() > self.max_message_size {
            return Err(RelayError::MessageTooLarge {
                size: payload.len(),
                max: self.max_message_size,
            });
        }
        if ttl_blocks == 0 || ttl_blocks > self.max_ttl {
            return Err(RelayError::InvalidTtl);
        }

        // Charge quota.
        let size = payload.len() as u64;
        let cost = self.bank.charge_relay(payer, size, ttl_blocks)?;

        // Create queue entry.
        let content_hash = *blake3::hash(&payload).as_bytes();
        let entry = QueueEntry {
            content_hash,
            sender: *payer_to_sender(payer),
            deposit: cost,
            enqueued_at: self.current_block,
            size: payload.len(),
        };

        // Get or create queue for this destination.
        let cap = self.default_queue_capacity;
        let queue = self
            .queues
            .entry(destination)
            .or_insert_with(|| MerkleQueue::new(cap));

        let new_root = queue.enqueue(entry)?;

        // Track metadata for GC.
        self.metadata
            .entry(destination)
            .or_default()
            .push(MessageMeta {
                enqueued_at: self.current_block,
                ttl_blocks,
                payer: *payer,
                cost_paid: cost,
                size: payload.len(),
            });

        Ok(new_root)
    }

    /// Drain all messages for a destination (delivery).
    /// Returns entries with dequeue proofs for verification.
    pub fn drain(&mut self, destination: &[u8; 32]) -> Vec<(QueueEntry, DequeueProof)> {
        let mut results = Vec::new();

        if let Some(queue) = self.queues.get_mut(destination) {
            while let Ok((entry, proof)) = queue.dequeue() {
                results.push((entry, proof));
            }
        }

        // Clean up empty queues.
        if let Some(q) = self.queues.get(destination)
            && q.is_empty()
        {
            self.queues.remove(destination);
        }
        self.metadata.remove(destination);

        results
    }

    /// Drain returning MeteredMessage (legacy compatibility).
    pub fn drain_messages(&mut self, destination: &[u8; 32]) -> Vec<MeteredMessage> {
        let entries = self.drain(destination);
        let metas = self.metadata.remove(destination).unwrap_or_default();

        entries
            .into_iter()
            .enumerate()
            .map(|(i, (entry, _proof))| {
                let meta = metas.get(i).cloned().unwrap_or(MessageMeta {
                    enqueued_at: entry.enqueued_at,
                    ttl_blocks: 0,
                    payer: QuotaId(0),
                    cost_paid: entry.deposit,
                    size: entry.size,
                });
                MeteredMessage {
                    destination: *destination,
                    payload: Vec::new(), // Content not stored in queue entries
                    enqueued_at: meta.enqueued_at,
                    ttl_blocks: meta.ttl_blocks,
                    payer: meta.payer,
                    cost_paid: meta.cost_paid,
                }
            })
            .collect()
    }

    /// Garbage-collect expired messages. Returns refunds for each expired message.
    /// Expired messages get a partial refund (proportional to unused TTL).
    pub fn gc_expired(&mut self, current_block: u64) -> Vec<ComputronRefund> {
        self.current_block = current_block;
        let mut refunds = Vec::new();

        let destinations: Vec<[u8; 32]> = self.queues.keys().copied().collect();

        for dest in destinations {
            // Check metadata for expired entries at the head of the queue.
            loop {
                let should_dequeue = if let Some(metas) = self.metadata.get(&dest) {
                    if let Some(meta) = metas.first() {
                        let expires_at = meta.enqueued_at + meta.ttl_blocks;
                        current_block >= expires_at
                    } else {
                        false
                    }
                } else {
                    false
                };

                if !should_dequeue {
                    break;
                }

                // Dequeue the expired entry.
                if let Some(queue) = self.queues.get_mut(&dest) {
                    if queue.dequeue().is_ok() {
                        if let Some(metas) = self.metadata.get_mut(&dest)
                            && !metas.is_empty()
                        {
                            let meta = metas.remove(0);
                            // 10% refund on expiry.
                            let refund_amount = (meta.cost_paid as f64 * 0.1) as u64;
                            if refund_amount > 0 {
                                if let Ok(cell) = self.bank.get_mut(&meta.payer) {
                                    cell.refund(refund_amount);
                                }
                                refunds.push(ComputronRefund {
                                    quota_id: meta.payer,
                                    amount: refund_amount,
                                });
                            }
                        }
                    } else {
                        break;
                    }
                } else {
                    break;
                }
            }
        }

        // Remove empty queues.
        self.queues.retain(|_, q| !q.is_empty());
        self.metadata.retain(|_, m| !m.is_empty());

        refunds
    }

    /// Total number of buffered messages across all destinations.
    pub fn total_buffered(&self) -> usize {
        self.queues.values().map(|q| q.len()).sum()
    }

    /// Number of messages buffered for a specific destination.
    pub fn buffered_for(&self, destination: &[u8; 32]) -> usize {
        self.queues.get(destination).map(|q| q.len()).unwrap_or(0)
    }

    /// Advance the block height.
    pub fn advance_block(&mut self, new_block: u64) {
        self.current_block = new_block;
    }

    /// Get the queue root for a destination (verifiable commitment).
    pub fn queue_root(&self, destination: &[u8; 32]) -> Option<[u8; 32]> {
        self.queues.get(destination).map(|q| q.root())
    }

    /// Get total bytes buffered in the relay (estimated from metadata).
    pub fn total_bytes_buffered(&self) -> u64 {
        self.metadata
            .values()
            .flat_map(|m| m.iter())
            .map(|m| m.size as u64)
            .sum()
    }
}

/// Helper: derive a sender identity from a QuotaId.
/// In a real system this would be a proper identity lookup.
fn payer_to_sender(_payer: &QuotaId) -> &[u8; 32] {
    // QuotaId is a u64; we use a static zero-filled array and override conceptually.
    // For Phase 4 the sender field tracks the payer's quota ID encoded as bytes.
    static ZERO: [u8; 32] = [0u8; 32];
    &ZERO
}

// =============================================================================
// TODO: CapTP store-and-forward integration
// =============================================================================
//
// The `captp/src/store_forward.rs` MessageRelay currently uses VecDeque<QueuedMessage>.
// The mapping to this module is:
//
//   MessageRelay::enqueue(msg)  ->  MeteredRelay::enqueue(dest, payload, ttl, payer)
//                                   OR RelayOperator::receive_message(dest, msg, deposit)
//
//   MessageRelay::drain(dest)   ->  MeteredRelay::drain(dest)
//                                   OR RelayOperator::drain_for_owner(owner, max)
//
//   MessageRelay::expire(h)     ->  MeteredRelay::gc_expired(h)
//                                   OR RelayOperator::gc_expired(h, ttl)
//
// The key difference: MeteredRelay/RelayOperator returns DequeueProofs on drain,
// enabling cryptographic verification of delivery. MessageRelay just returns messages.
//
// Migration path:
// 1. Add a `MerkleBackedRelay` wrapper in captp that delegates to pyana-storage
// 2. The wrapper translates QueuedMessage -> InboxMessage for enqueue
// 3. On drain, wrapper returns QueuedMessage + DequeueProof pairs
// 4. Existing tests continue to pass with the VecDeque-based MessageRelay
// 5. New tests verify the Merkle-backed path with proof verification

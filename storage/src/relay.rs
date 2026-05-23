//! Metered store-and-forward relay.
//!
//! Wraps the captp store-and-forward concept with resource accounting.
//! Every message buffered for an offline destination costs computrons.
//! The relay node is providing a SERVICE (storage + eventual delivery).
//! If the sender's quota is exhausted, messages are rejected.
//! TTL-based pricing: longer TTL = more expensive (rent model).

use std::collections::{HashMap, VecDeque};

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
}

impl From<StorageError> for RelayError {
    fn from(e: StorageError) -> Self {
        match e {
            StorageError::QuotaExhausted { available, required } => {
                RelayError::QuotaExhausted { available, required }
            }
            StorageError::QuotaNotFound(id) => RelayError::QuotaNotFound(id),
            _ => RelayError::QuotaExhausted {
                available: 0,
                required: 0,
            },
        }
    }
}

/// Metered store-and-forward relay node.
#[derive(Debug)]
pub struct MeteredRelay {
    /// Per-destination message queues.
    queues: HashMap<[u8; 32], VecDeque<MeteredMessage>>,
    /// The space bank governing quota for relay operations.
    pub bank: SpaceBank,
    /// Maximum message size in bytes.
    pub max_message_size: usize,
    /// Maximum TTL in blocks.
    pub max_ttl: u64,
    /// Current block height (for expiry).
    pub current_block: u64,
}

impl MeteredRelay {
    /// Create a new metered relay with the given space bank.
    pub fn new(bank: SpaceBank, max_message_size: usize, max_ttl: u64) -> Self {
        Self {
            queues: HashMap::new(),
            bank,
            max_message_size,
            max_ttl,
            current_block: 0,
        }
    }

    /// Enqueue a message for buffered delivery.
    /// Charges the payer's quota based on message size and TTL.
    pub fn enqueue(
        &mut self,
        destination: [u8; 32],
        payload: Vec<u8>,
        ttl_blocks: u64,
        payer: &QuotaId,
    ) -> Result<(), RelayError> {
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

        // Enqueue.
        let msg = MeteredMessage {
            destination,
            payload,
            enqueued_at: self.current_block,
            ttl_blocks,
            payer: *payer,
            cost_paid: cost,
        };

        self.queues
            .entry(destination)
            .or_insert_with(VecDeque::new)
            .push_back(msg);

        Ok(())
    }

    /// Drain all messages for a destination (delivery).
    /// The destination has come online and is collecting its messages.
    pub fn drain(&mut self, destination: &[u8; 32]) -> Vec<MeteredMessage> {
        self.queues
            .remove(destination)
            .map(|q| q.into_iter().collect())
            .unwrap_or_default()
    }

    /// Garbage-collect expired messages. Returns refunds for each expired message.
    /// Expired messages get a partial refund (proportional to unused TTL).
    pub fn gc_expired(&mut self, current_block: u64) -> Vec<ComputronRefund> {
        self.current_block = current_block;
        let mut refunds = Vec::new();

        for (_dest, queue) in self.queues.iter_mut() {
            let mut i = 0;
            while i < queue.len() {
                let msg = &queue[i];
                let expires_at = msg.enqueued_at + msg.ttl_blocks;
                if current_block >= expires_at {
                    let msg = queue.remove(i).unwrap();
                    // Partial refund: fraction of TTL unused.
                    // Since it expired, the full TTL was used — minimal refund.
                    // But the relay node kept the data — refund the "delivery" portion.
                    let refund_amount = (msg.cost_paid as f64 * 0.1) as u64; // 10% on expiry
                    if refund_amount > 0 {
                        // Apply refund to the payer's quota.
                        if let Ok(cell) = self.bank.get_mut(&msg.payer) {
                            cell.refund(refund_amount);
                        }
                        refunds.push(ComputronRefund {
                            quota_id: msg.payer,
                            amount: refund_amount,
                        });
                    }
                } else {
                    i += 1;
                }
            }
        }

        // Remove empty queues.
        self.queues.retain(|_, q| !q.is_empty());

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

    /// Get total bytes buffered in the relay.
    pub fn total_bytes_buffered(&self) -> u64 {
        self.queues
            .values()
            .flat_map(|q| q.iter())
            .map(|m| m.payload.len() as u64)
            .sum()
    }
}

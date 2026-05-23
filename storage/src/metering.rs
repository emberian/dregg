//! Computron cost model for storage operations.
//!
//! Every storage operation has a computron cost:
//! - Write: base_cost + (size_bytes * cost_per_byte)
//! - Read: free (already paid at write time) OR: read_cost_per_byte (if metering reads)
//! - Splice: cost of old deletion + cost of new write
//! - Delete: refunds refund_rate * original_write_cost
//! - Relay buffer: cost_per_message + (size * cost_per_byte * ttl_blocks)
//!
//! The key insight: storage is RENTED, not bought. You pay per-epoch for bytes stored.
//! If you stop paying (quota depleted), your data becomes eligible for GC.
//! This prevents unbounded storage accumulation.

/// Policy governing computron costs for storage operations.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct MeteringPolicy {
    /// Base cost for any write (covers indexing overhead).
    pub write_base_cost: u64,
    /// Per-byte cost for writes.
    pub write_cost_per_byte: u64,
    /// Per-byte cost for reads (0 = reads are free).
    pub read_cost_per_byte: u64,
    /// Base cost for relay message buffering.
    pub relay_base_cost: u64,
    /// Per-byte cost multiplied by TTL for relay.
    pub relay_cost_per_byte_block: u64,
    /// Fraction refunded on deletion (0.0 to 1.0).
    pub refund_rate: f64,
    /// Per-byte rental cost per epoch for stored data.
    pub rental_cost_per_byte_epoch: u64,
}

impl MeteringPolicy {
    /// A reasonable default policy for prototyping.
    pub fn default_policy() -> Self {
        Self {
            write_base_cost: 100,
            write_cost_per_byte: 10,
            read_cost_per_byte: 0,
            relay_base_cost: 50,
            relay_cost_per_byte_block: 5,
            refund_rate: 0.8,
            rental_cost_per_byte_epoch: 1,
        }
    }

    /// Compute cost for a storage operation.
    pub fn compute_cost(&self, op: &StorageOp) -> u64 {
        match op {
            StorageOp::Write { size } => self.write_base_cost + (size * self.write_cost_per_byte),
            StorageOp::Read { size } => size * self.read_cost_per_byte,
            StorageOp::Splice { old_size, new_size } => {
                // Splice = cost of deleting old + writing new.
                // The refund from old is handled at a higher level.
                let delete_refund = self.compute_refund(&StorageOp::Write { size: *old_size });
                let new_write_cost =
                    self.write_base_cost + (new_size * self.write_cost_per_byte);
                // Net cost = new write cost - refund from old
                new_write_cost.saturating_sub(delete_refund)
            }
            StorageOp::Delete { size } => {
                // Deletion itself is free; the refund is computed separately.
                // But there is a small processing cost.
                let _ = size;
                0
            }
            StorageOp::Relay { size, ttl_blocks } => {
                self.relay_base_cost + (size * self.relay_cost_per_byte_block * ttl_blocks)
            }
            StorageOp::Rental { bytes, epochs } => {
                bytes * self.rental_cost_per_byte_epoch * epochs
            }
            StorageOp::Enqueue { size, deposit } => {
                // Cost = base write cost for the message + deposit transferred to recipient.
                // The deposit is held (not consumed), but the write cost is real.
                self.write_base_cost + (size * self.write_cost_per_byte) + deposit
            }
            StorageOp::Dequeue { size } => {
                // Dequeue is free for the reader (sender already paid).
                // Small processing cost for Merkle root recomputation.
                let _ = size;
                0
            }
            StorageOp::CreateQueue { capacity } => {
                // Cost = base cost + capacity reservation cost.
                // Reserve space for `capacity` entries worth of metadata overhead.
                self.write_base_cost + (capacity * self.write_cost_per_byte)
            }
            StorageOp::ResizeQueue {
                old_capacity,
                new_capacity,
            } => {
                // Growing costs the delta. Shrinking is free (refund handled elsewhere).
                if new_capacity > old_capacity {
                    let delta = new_capacity - old_capacity;
                    delta * self.write_cost_per_byte
                } else {
                    0
                }
            }
        }
    }

    /// Compute refund for deleting content that was written with the given op cost.
    pub fn compute_refund(&self, original_write_op: &StorageOp) -> u64 {
        let original_cost = match original_write_op {
            StorageOp::Write { size } => {
                self.write_base_cost + (size * self.write_cost_per_byte)
            }
            _ => 0,
        };
        (original_cost as f64 * self.refund_rate) as u64
    }

    /// Compute per-epoch rental cost for a given byte count.
    pub fn epoch_rental_cost(&self, bytes_stored: u64) -> u64 {
        bytes_stored * self.rental_cost_per_byte_epoch
    }
}

/// A storage operation for cost computation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StorageOp {
    Write { size: u64 },
    Read { size: u64 },
    Splice { old_size: u64, new_size: u64 },
    Delete { size: u64 },
    Relay { size: u64, ttl_blocks: u64 },
    /// Rental cost for storing `bytes` for `epochs`.
    Rental { bytes: u64, epochs: u64 },
    /// Enqueue a message into a MerkleQueue.
    Enqueue { size: u64, deposit: u64 },
    /// Dequeue a message from a MerkleQueue.
    Dequeue { size: u64 },
    /// Create a new MerkleQueue with given capacity.
    CreateQueue { capacity: u64 },
    /// Resize an existing MerkleQueue.
    ResizeQueue { old_capacity: u64, new_capacity: u64 },
}

/// Compute cost for a storage operation given a policy.
pub fn compute_cost(policy: &MeteringPolicy, op: &StorageOp) -> u64 {
    policy.compute_cost(op)
}

/// Compute refund for a deletion given the original write op.
pub fn compute_refund(policy: &MeteringPolicy, original_write_op: &StorageOp) -> u64 {
    policy.compute_refund(original_write_op)
}

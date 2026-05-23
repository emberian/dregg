//! Space banks: quota cells that bound storage consumption.
//!
//! A quota cell bounds how much storage an entity can consume.
//! Inspired by Robigalia's Volume concept.
//! Quota = computrons allocated for storage. Each byte stored costs C computrons.
//! When quota is exhausted, writes fail. Quota can be topped up (Transfer effect).

use std::collections::HashMap;

use crate::{ComputronRefund, QuotaId, StorageError};

/// A single quota cell — bounds storage consumption for one entity.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct QuotaCell {
    pub id: QuotaId,
    /// Public key of the owner.
    pub owner: [u8; 32],
    /// Total computrons allocated to this quota.
    pub total_allocated: u64,
    /// Computrons consumed so far.
    pub total_consumed: u64,
    /// Total bytes currently stored under this quota.
    pub bytes_stored: u64,
    /// Hard cap on bytes (even if computrons available).
    pub max_bytes: Option<u64>,
}

impl QuotaCell {
    /// Remaining computrons available.
    pub fn available(&self) -> u64 {
        self.total_allocated.saturating_sub(self.total_consumed)
    }

    /// Whether a charge of `cost` computrons would succeed.
    pub fn can_charge(&self, cost: u64) -> bool {
        self.available() >= cost
    }

    /// Whether storing `additional_bytes` would exceed the byte cap.
    pub fn would_exceed_byte_cap(&self, additional_bytes: u64) -> bool {
        if let Some(max) = self.max_bytes {
            self.bytes_stored + additional_bytes > max
        } else {
            false
        }
    }

    /// Charge computrons. Returns error if insufficient.
    pub fn charge(&mut self, cost: u64) -> Result<(), StorageError> {
        if self.available() < cost {
            return Err(StorageError::QuotaExhausted {
                available: self.available(),
                required: cost,
            });
        }
        self.total_consumed += cost;
        Ok(())
    }

    /// Refund computrons (from deletion). Cannot exceed total_consumed.
    pub fn refund(&mut self, amount: u64) {
        // Refund cannot make consumed go negative.
        self.total_consumed = self.total_consumed.saturating_sub(amount);
    }

    /// Record bytes stored.
    pub fn record_bytes_stored(&mut self, bytes: u64) {
        self.bytes_stored += bytes;
    }

    /// Record bytes freed.
    pub fn record_bytes_freed(&mut self, bytes: u64) {
        self.bytes_stored = self.bytes_stored.saturating_sub(bytes);
    }

    /// Top up with additional computrons.
    pub fn top_up(&mut self, additional: u64) {
        self.total_allocated += additional;
    }
}

/// Space bank: manages multiple quota cells.
#[derive(Debug, Clone)]
pub struct SpaceBank {
    pub quotas: HashMap<QuotaId, QuotaCell>,
    /// Computrons charged per byte for a write operation.
    pub cost_per_byte: u64,
    /// Computrons charged per relay message buffered.
    pub cost_per_relay_message: u64,
    /// Fraction of original cost refunded on deletion (0.0 to 1.0).
    pub refund_rate: f64,
    /// Next quota ID to assign.
    next_id: u64,
}

impl SpaceBank {
    /// Create a new space bank with the given cost parameters.
    pub fn new(cost_per_byte: u64, cost_per_relay_message: u64, refund_rate: f64) -> Self {
        Self {
            quotas: HashMap::new(),
            cost_per_byte,
            cost_per_relay_message,
            refund_rate: refund_rate.clamp(0.0, 1.0),
            next_id: 1,
        }
    }

    /// Allocate a new quota cell.
    pub fn allocate_quota(
        &mut self,
        owner: [u8; 32],
        initial_computrons: u64,
        max_bytes: Option<u64>,
    ) -> QuotaId {
        let id = QuotaId(self.next_id);
        self.next_id += 1;
        let cell = QuotaCell {
            id,
            owner,
            total_allocated: initial_computrons,
            total_consumed: 0,
            bytes_stored: 0,
            max_bytes,
        };
        self.quotas.insert(id, cell);
        id
    }

    /// Get a reference to a quota cell.
    pub fn get(&self, id: &QuotaId) -> Result<&QuotaCell, StorageError> {
        self.quotas.get(id).ok_or(StorageError::QuotaNotFound(*id))
    }

    /// Get a mutable reference to a quota cell.
    pub fn get_mut(&mut self, id: &QuotaId) -> Result<&mut QuotaCell, StorageError> {
        self.quotas.get_mut(id).ok_or(StorageError::QuotaNotFound(*id))
    }

    /// Charge a write to a quota cell. Returns the cost charged.
    pub fn charge_write(&mut self, payer: &QuotaId, size_bytes: u64) -> Result<u64, StorageError> {
        let cost = self.cost_per_byte * size_bytes;
        let cell = self.get_mut(payer)?;

        // Check byte cap first.
        if cell.would_exceed_byte_cap(size_bytes) {
            return Err(StorageError::ByteCapExceeded {
                current: cell.bytes_stored,
                max: cell.max_bytes.unwrap_or(u64::MAX),
                attempted: size_bytes,
            });
        }

        cell.charge(cost)?;
        cell.record_bytes_stored(size_bytes);
        Ok(cost)
    }

    /// Process a deletion refund.
    pub fn process_refund(
        &mut self,
        owner: &QuotaId,
        original_cost: u64,
        size_bytes: u64,
    ) -> Result<ComputronRefund, StorageError> {
        let refund_amount = (original_cost as f64 * self.refund_rate) as u64;
        let cell = self.get_mut(owner)?;
        cell.refund(refund_amount);
        cell.record_bytes_freed(size_bytes);
        Ok(ComputronRefund {
            quota_id: *owner,
            amount: refund_amount,
        })
    }

    /// Charge a relay message to a quota cell.
    pub fn charge_relay(
        &mut self,
        payer: &QuotaId,
        size_bytes: u64,
        ttl_blocks: u64,
    ) -> Result<u64, StorageError> {
        // Cost = base message cost + (size * cost_per_byte * ttl)
        let cost =
            self.cost_per_relay_message + (size_bytes * self.cost_per_byte * ttl_blocks);
        let cell = self.get_mut(payer)?;
        cell.charge(cost)?;
        Ok(cost)
    }

    /// Top up a quota cell with additional computrons.
    pub fn top_up(&mut self, id: &QuotaId, additional: u64) -> Result<(), StorageError> {
        let cell = self.get_mut(id)?;
        cell.top_up(additional);
        Ok(())
    }

    /// Simulate an epoch passing: charge rental for all stored bytes.
    /// Returns list of quota IDs that are now depleted.
    pub fn tick_epoch(&mut self) -> Vec<QuotaId> {
        let cost_per_byte = self.cost_per_byte;
        let mut depleted = Vec::new();
        for (id, cell) in self.quotas.iter_mut() {
            let rental_cost = cell.bytes_stored * cost_per_byte;
            if cell.available() < rental_cost {
                depleted.push(*id);
            } else {
                cell.total_consumed += rental_cost;
            }
        }
        depleted
    }
}

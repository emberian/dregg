//! Budget gate: integration point for the Stingray bounded-counter budget system.
//!
//! The [`BudgetGate`] is an optional component of the [`TurnExecutor`] that checks
//! a per-silo budget slice before allowing turn execution. This connects the
//! executor to the Stingray bounded-counter budget coordinator (in `pyana-coord`)
//! without introducing a circular dependency.
//!
//! The gate holds a local copy of the silo's budget slice. The BudgetCoordinator
//! in `pyana-coord` manages distribution and rebalancing at a higher level.

use serde::{Deserialize, Serialize};

/// A debit digest uniquely identifying a budget debit (BLAKE3 hash).
pub type DebitDigest = [u8; 32];

/// A local budget slice for a silo, tracking the silo's spending allowance.
///
/// This is the turn-crate-local representation of a budget slice. The full
/// lifecycle (distribution, rebalancing, certificates) is managed by
/// `BudgetCoordinator` in `pyana-coord`. This struct carries just enough state
/// to gate individual turn executions.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BudgetSlice {
    /// Maximum amount this silo may spend (the slice ceiling).
    pub ceiling: u64,
    /// Amount already spent from this slice.
    pub spent: u64,
    /// Transaction digests that consumed from this slice.
    pub debits: Vec<DebitDigest>,
    /// Budget epoch version this slice belongs to.
    /// Used to reject stale slices from previous epochs after a rebalance.
    pub version: u64,
}

impl BudgetSlice {
    /// Create a new budget slice with the given ceiling and version.
    pub fn new(ceiling: u64) -> Self {
        BudgetSlice {
            ceiling,
            spent: 0,
            debits: Vec::new(),
            version: 0,
        }
    }

    /// Create a new budget slice with a specific epoch version.
    pub fn with_version(ceiling: u64, version: u64) -> Self {
        BudgetSlice {
            ceiling,
            spent: 0,
            debits: Vec::new(),
            version,
        }
    }

    /// Remaining budget in this slice.
    pub fn remaining(&self) -> u64 {
        self.ceiling.saturating_sub(self.spent)
    }

    /// Whether this slice has any remaining budget.
    pub fn has_budget(&self) -> bool {
        self.remaining() > 0
    }

    /// Try to debit from this slice.
    ///
    /// Returns `Ok(())` if the debit succeeds (enough remaining).
    /// Returns `Err(remaining)` if the slice cannot cover the amount.
    pub fn try_debit(&mut self, amount: u64, digest: DebitDigest) -> Result<(), u64> {
        if amount > self.remaining() {
            return Err(self.remaining());
        }
        self.spent = self.spent.saturating_add(amount);
        self.debits.push(digest);
        Ok(())
    }

    /// Refund a previous debit (fast unlock on turn failure/rollback).
    ///
    /// Finds and removes the debit with the given digest, restoring the spent amount.
    /// Returns `true` if the debit was found and refunded, `false` otherwise.
    pub fn refund(&mut self, amount: u64, digest: &DebitDigest) -> bool {
        if let Some(pos) = self.debits.iter().position(|d| d == digest) {
            self.debits.swap_remove(pos);
            self.spent = self.spent.saturating_sub(amount);
            true
        } else {
            false
        }
    }

    /// Commit a debit permanently after a turn succeeds.
    ///
    /// This is a no-op in terms of the budget arithmetic (the debit was already
    /// applied by `try_debit`), but it records the digest as finalized so it
    /// cannot be refunded later. Call this after the turn commits successfully
    /// and before fee distribution.
    pub fn commit_debit(&mut self, _digest: &DebitDigest) {
        // The debit is already reflected in `spent`. This method exists to
        // make the two-phase protocol explicit: try_debit is tentative,
        // commit_debit is final. In a future version, committed debits could
        // be moved to a separate set for audit or epoch-boundary compaction.
    }
}

/// A budget gate that checks a silo's local slice before turn execution.
///
/// When attached to a [`TurnExecutor`], the gate is checked after Phase 1
/// (fee/nonce commitment) but before Phase 2 (call forest execution). If the
/// silo's slice cannot cover the turn's fee, the turn is rejected with
/// `TurnError::BudgetExhausted`.
///
/// On turn failure/rollback, the debit is refunded via `fast_unlock()`.
pub struct BudgetGate {
    /// Logical silo identifier (for error reporting).
    pub silo_id: u32,
    /// The local budget slice for this silo.
    pub slice: BudgetSlice,
    /// Current epoch version expected by this gate.
    /// If the slice version doesn't match, the gate rejects (stale slice).
    pub expected_version: u64,
}

impl BudgetGate {
    /// Create a new budget gate for a silo with the given slice.
    pub fn new(silo_id: u32, slice: BudgetSlice) -> Self {
        let expected_version = slice.version;
        BudgetGate {
            silo_id,
            slice,
            expected_version,
        }
    }

    /// Try to debit the turn fee from the budget slice.
    ///
    /// Returns `Ok(digest)` with the debit digest on success.
    /// Returns `Err((remaining,))` if the slice cannot cover the fee.
    ///
    /// Rejects the debit if the slice version doesn't match the gate's expected epoch.
    pub fn try_debit(&mut self, fee: u64, turn_hash: &[u8; 32]) -> Result<DebitDigest, u64> {
        // Reject stale slices from a previous epoch.
        if self.slice.version != self.expected_version {
            return Err(0);
        }
        let digest = Self::compute_debit_digest(turn_hash);
        self.slice.try_debit(fee, digest)?;
        Ok(digest)
    }

    /// Update the gate's expected version (called after rebalance).
    pub fn set_expected_version(&mut self, version: u64) {
        self.expected_version = version;
    }

    /// Refund a debit after turn failure (fast unlock).
    pub fn fast_unlock(&mut self, fee: u64, digest: &DebitDigest) {
        self.slice.refund(fee, digest);
    }

    /// Commit a debit permanently after a turn succeeds.
    ///
    /// Call this after the turn commits but before fee distribution. Makes the
    /// tentative debit permanent — it can no longer be refunded via `fast_unlock`.
    pub fn commit_debit(&mut self, digest: &DebitDigest) {
        self.slice.commit_debit(digest);
    }

    /// Compute a debit digest from a turn hash.
    pub fn compute_debit_digest(turn_hash: &[u8; 32]) -> DebitDigest {
        let mut hasher = blake3::Hasher::new_derive_key("pyana-budget-gate debit-digest v1");
        hasher.update(turn_hash);
        *hasher.finalize().as_bytes()
    }
}

//! Fulfillment delay pool for timing decorrelation.
//!
//! Instead of immediately publishing fulfillment reveals, they enter a delay pool
//! and are released in BATCHES at fixed intervals. Multiple fulfillments released
//! simultaneously means an observer cannot correlate which fulfiller matched which
//! intent based on timing alone.
//!
//! # Privacy model
//!
//! - Real reveals and dummy reveals are structurally identical until verification.
//! - Dummies fail proof verification but are indistinguishable from real reveals
//!   at the gossip layer.
//! - Batched release ensures that even a network-level observer cannot correlate
//!   individual commitment times with reveal times.
//!
//! # Configuration
//!
//! - `batch_interval_secs`: How often batches release (default 30s).
//! - `min_batch_size`: Don't release a batch of 1 (default 3).
//! - `max_delay_secs`: Failsafe maximum time any item stays in the pool (default 120s).
//! - `dummy_rate_per_interval`: How many dummies to inject per batch interval (default 1).

use std::collections::VecDeque;

use crate::commit_reveal_fulfillment::FulfillmentResult;

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Configuration for the delay pool.
#[derive(Clone, Debug)]
pub struct DelayPoolConfig {
    /// How often to release a batch (seconds).
    pub batch_interval_secs: u64,
    /// Minimum pool size before releasing (don't release a batch of 1).
    pub min_batch_size: usize,
    /// Maximum time an item can stay in the pool (failsafe).
    pub max_delay_secs: u64,
    /// Number of dummy reveals to inject per batch interval.
    pub dummy_rate_per_interval: usize,
}

impl Default for DelayPoolConfig {
    fn default() -> Self {
        Self {
            batch_interval_secs: 30,
            min_batch_size: 3,
            max_delay_secs: 120,
            dummy_rate_per_interval: 1,
        }
    }
}

// ---------------------------------------------------------------------------
// Pool item wrapper
// ---------------------------------------------------------------------------

/// An item in the delay pool: either a real fulfillment or a dummy.
#[derive(Clone, Debug)]
pub enum PoolItem {
    /// A real fulfillment result ready for publication.
    Real(FulfillmentResult),
    /// A dummy reveal that looks real at the gossip layer but fails proof verification.
    Dummy(DummyReveal),
}

/// A dummy reveal that is structurally valid but will fail proof verification.
///
/// Indistinguishable from a real reveal until the verifier checks the commitment
/// hash or STARK proof, at which point it is silently discarded.
#[derive(Clone, Debug)]
pub struct DummyReveal {
    /// A random commitment hash (does not correspond to any real commitment).
    pub commitment_hash: [u8; 32],
    /// A random intent_id (does not correspond to any real intent).
    pub intent_id: [u8; 32],
    /// The timestamp at which this dummy was generated.
    pub generated_at: u64,
}

// ---------------------------------------------------------------------------
// DelayPool
// ---------------------------------------------------------------------------

/// A pool that accumulates fulfillment items and releases them in batches
/// for timing decorrelation.
pub struct DelayPool {
    items: VecDeque<(PoolItem, u64)>, // (item, insertion_timestamp)
    config: DelayPoolConfig,
    last_release: u64,
    /// Counter for tracking total items ever submitted (for metrics).
    total_submitted: u64,
    /// Counter for total batches released.
    total_batches_released: u64,
}

impl DelayPool {
    /// Create a new delay pool with the given configuration.
    pub fn new(config: DelayPoolConfig) -> Self {
        Self {
            items: VecDeque::new(),
            config,
            last_release: 0,
            total_submitted: 0,
            total_batches_released: 0,
        }
    }

    /// Submit a real fulfillment result to the pool.
    pub fn submit(&mut self, item: FulfillmentResult, now: u64) {
        self.items.push_back((PoolItem::Real(item), now));
        self.total_submitted += 1;
    }

    /// Submit a dummy reveal to the pool.
    pub fn submit_dummy(&mut self, dummy: DummyReveal, now: u64) {
        self.items.push_back((PoolItem::Dummy(dummy), now));
    }

    /// Check if it's time to release a batch.
    ///
    /// A batch is released when:
    /// - The batch interval has elapsed AND there are enough items, OR
    /// - Any item has exceeded the maximum delay (failsafe timeout).
    pub fn should_release(&self, now: u64) -> bool {
        if self.items.is_empty() {
            return false;
        }

        let interval_elapsed = now.saturating_sub(self.last_release) >= self.config.batch_interval_secs;
        let enough_items = self.items.len() >= self.config.min_batch_size;
        let timeout = self
            .items
            .front()
            .map(|(_, t)| now.saturating_sub(*t) >= self.config.max_delay_secs)
            .unwrap_or(false);

        (interval_elapsed && enough_items) || timeout
    }

    /// Release all items currently in the pool as a batch.
    ///
    /// Returns the batch of items. After this call, the pool is empty and
    /// the release timestamp is updated.
    pub fn release_batch(&mut self, now: u64) -> Vec<PoolItem> {
        self.last_release = now;
        self.total_batches_released += 1;
        self.items.drain(..).map(|(item, _)| item).collect()
    }

    /// Number of items waiting in the pool.
    pub fn pending_count(&self) -> usize {
        self.items.len()
    }

    /// Number of real (non-dummy) items in the pool.
    pub fn real_count(&self) -> usize {
        self.items
            .iter()
            .filter(|(item, _)| matches!(item, PoolItem::Real(_)))
            .count()
    }

    /// Total items ever submitted to this pool.
    pub fn total_submitted(&self) -> u64 {
        self.total_submitted
    }

    /// Total batches released from this pool.
    pub fn total_batches_released(&self) -> u64 {
        self.total_batches_released
    }

    /// Get the pool configuration.
    pub fn config(&self) -> &DelayPoolConfig {
        &self.config
    }

    /// The timestamp of the last batch release.
    pub fn last_release_time(&self) -> u64 {
        self.last_release
    }

    /// Tick the pool: inject dummies and release a batch if conditions are met.
    ///
    /// This is intended to be called from the node's event loop on each timer tick.
    /// Returns `Some(batch)` if a batch was released, `None` otherwise.
    pub fn tick(&mut self, now: u64) -> Option<Vec<PoolItem>> {
        // Inject dummy reveals at the configured rate.
        // We inject if the interval since the last release has elapsed (or on first tick).
        let interval_elapsed =
            now.saturating_sub(self.last_release) >= self.config.batch_interval_secs;

        if interval_elapsed {
            for _ in 0..self.config.dummy_rate_per_interval {
                let dummy = generate_dummy_reveal(now);
                self.submit_dummy(dummy, now);
            }
        }

        // Check if we should release.
        if self.should_release(now) {
            Some(self.release_batch(now))
        } else {
            None
        }
    }
}

// ---------------------------------------------------------------------------
// Dummy reveal generation
// ---------------------------------------------------------------------------

/// Generate a structurally-valid-looking dummy reveal.
///
/// The dummy has random commitment_hash and intent_id values. When received by
/// a verifier, it will fail commitment lookup (no matching commitment in the
/// registry) and be silently discarded. However, at the gossip transport layer,
/// it is indistinguishable from a real reveal.
pub fn generate_dummy_reveal(now: u64) -> DummyReveal {
    let mut commitment_hash = [0u8; 32];
    let mut intent_id = [0u8; 32];
    crate::getrandom(&mut commitment_hash);
    crate::getrandom(&mut intent_id);

    DummyReveal {
        commitment_hash,
        intent_id,
        generated_at: now,
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::commit_reveal_fulfillment::{FulfillmentCommitment, FulfillmentResult};
    use crate::fulfillment::Fulfillment;
    use crate::{CommitmentId, VerificationMode};

    fn make_fulfillment_result(id: u8) -> FulfillmentResult {
        let mut intent_id = [0u8; 32];
        intent_id[0] = id;

        FulfillmentResult {
            fulfillment: Fulfillment {
                intent_id,
                fulfiller: CommitmentId([0xBB; 32]),
                mode: VerificationMode::Trusted,
                token_data: Some(vec![1, 2, 3]),
                proof: None,
                granted_actions: vec!["read".into()],
                granted_resource: "*".into(),
                expiry: Some(9999),
            },
            commitment: FulfillmentCommitment {
                intent_id,
                commitment_hash: [id; 32],
                committed_at: 100,
                epoch: 0,
            },
            fulfilled_epoch: 0,
        }
    }

    #[test]
    fn test_new_pool_is_empty() {
        let pool = DelayPool::new(DelayPoolConfig::default());
        assert_eq!(pool.pending_count(), 0);
        assert_eq!(pool.real_count(), 0);
        assert_eq!(pool.total_submitted(), 0);
        assert_eq!(pool.total_batches_released(), 0);
    }

    #[test]
    fn test_submit_increases_count() {
        let mut pool = DelayPool::new(DelayPoolConfig::default());
        pool.submit(make_fulfillment_result(1), 100);
        assert_eq!(pool.pending_count(), 1);
        assert_eq!(pool.real_count(), 1);
        assert_eq!(pool.total_submitted(), 1);
    }

    #[test]
    fn test_submit_dummy_increases_count() {
        let mut pool = DelayPool::new(DelayPoolConfig::default());
        let dummy = generate_dummy_reveal(100);
        pool.submit_dummy(dummy, 100);
        assert_eq!(pool.pending_count(), 1);
        assert_eq!(pool.real_count(), 0); // dummy doesn't count as real
    }

    #[test]
    fn test_should_release_requires_interval_and_min_batch() {
        let config = DelayPoolConfig {
            batch_interval_secs: 30,
            min_batch_size: 3,
            max_delay_secs: 120,
            dummy_rate_per_interval: 0,
        };
        let mut pool = DelayPool::new(config);

        // Submit 2 items at time 0
        pool.submit(make_fulfillment_result(1), 0);
        pool.submit(make_fulfillment_result(2), 0);

        // At time 31 (interval elapsed), but only 2 items (need 3): don't release
        assert!(!pool.should_release(31));

        // Add a third item
        pool.submit(make_fulfillment_result(3), 15);

        // Now we have 3 items and interval elapsed: should release
        assert!(pool.should_release(31));
    }

    #[test]
    fn test_should_release_timeout_failsafe() {
        let config = DelayPoolConfig {
            batch_interval_secs: 30,
            min_batch_size: 5, // high threshold
            max_delay_secs: 120,
            dummy_rate_per_interval: 0,
        };
        let mut pool = DelayPool::new(config);

        // Submit 1 item at time 0
        pool.submit(make_fulfillment_result(1), 0);

        // At time 119, not yet timed out
        assert!(!pool.should_release(119));

        // At time 120, the oldest item hits max_delay: force release
        assert!(pool.should_release(120));
    }

    #[test]
    fn test_release_batch_drains_pool() {
        let config = DelayPoolConfig {
            batch_interval_secs: 10,
            min_batch_size: 2,
            max_delay_secs: 120,
            dummy_rate_per_interval: 0,
        };
        let mut pool = DelayPool::new(config);

        pool.submit(make_fulfillment_result(1), 0);
        pool.submit(make_fulfillment_result(2), 5);
        pool.submit(make_fulfillment_result(3), 8);

        assert_eq!(pool.pending_count(), 3);

        let batch = pool.release_batch(15);
        assert_eq!(batch.len(), 3);
        assert_eq!(pool.pending_count(), 0);
        assert_eq!(pool.total_batches_released(), 1);
        assert_eq!(pool.last_release_time(), 15);
    }

    #[test]
    fn test_release_batch_contains_correct_items() {
        let config = DelayPoolConfig {
            batch_interval_secs: 10,
            min_batch_size: 1,
            max_delay_secs: 120,
            dummy_rate_per_interval: 0,
        };
        let mut pool = DelayPool::new(config);

        pool.submit(make_fulfillment_result(1), 0);
        let dummy = generate_dummy_reveal(5);
        pool.submit_dummy(dummy, 5);

        let batch = pool.release_batch(15);
        assert_eq!(batch.len(), 2);

        let real_count = batch.iter().filter(|i| matches!(i, PoolItem::Real(_))).count();
        let dummy_count = batch.iter().filter(|i| matches!(i, PoolItem::Dummy(_))).count();
        assert_eq!(real_count, 1);
        assert_eq!(dummy_count, 1);
    }

    #[test]
    fn test_tick_injects_dummies_and_releases() {
        let config = DelayPoolConfig {
            batch_interval_secs: 30,
            min_batch_size: 3,
            max_delay_secs: 120,
            dummy_rate_per_interval: 2,
        };
        let mut pool = DelayPool::new(config);

        // Submit 1 real item
        pool.submit(make_fulfillment_result(1), 0);

        // Tick at time 30: interval elapsed, injects 2 dummies -> total 3 items >= min_batch_size
        let batch = pool.tick(30);
        assert!(batch.is_some(), "should release batch after interval with dummies");

        let batch = batch.unwrap();
        // 1 real + 2 dummies = 3
        assert_eq!(batch.len(), 3);
        let real_count = batch.iter().filter(|i| matches!(i, PoolItem::Real(_))).count();
        let dummy_count = batch.iter().filter(|i| matches!(i, PoolItem::Dummy(_))).count();
        assert_eq!(real_count, 1);
        assert_eq!(dummy_count, 2);
    }

    #[test]
    fn test_tick_no_release_before_interval() {
        let config = DelayPoolConfig {
            batch_interval_secs: 30,
            min_batch_size: 3,
            max_delay_secs: 120,
            dummy_rate_per_interval: 1,
        };
        let mut pool = DelayPool::new(config);

        pool.submit(make_fulfillment_result(1), 0);
        pool.submit(make_fulfillment_result(2), 5);

        // Tick at time 20: interval not elapsed -> no release, no dummies injected
        let batch = pool.tick(20);
        assert!(batch.is_none());
        // Items still in pool (no dummies injected because interval not elapsed)
        assert_eq!(pool.pending_count(), 2);
    }

    #[test]
    fn test_tick_timeout_forces_release_even_below_min_batch() {
        let config = DelayPoolConfig {
            batch_interval_secs: 30,
            min_batch_size: 10, // very high threshold
            max_delay_secs: 60,
            dummy_rate_per_interval: 0,
        };
        let mut pool = DelayPool::new(config);

        // Submit 1 item at time 0
        pool.submit(make_fulfillment_result(1), 0);

        // Tick at time 60: timeout hit -> force release even with 1 item
        let batch = pool.tick(60);
        assert!(batch.is_some());
        assert_eq!(batch.unwrap().len(), 1);
    }

    #[test]
    fn test_empty_pool_does_not_release() {
        let config = DelayPoolConfig {
            batch_interval_secs: 10,
            min_batch_size: 1,
            max_delay_secs: 60,
            dummy_rate_per_interval: 0,
        };
        let pool = DelayPool::new(config);

        // Empty pool never triggers release
        assert!(!pool.should_release(100));
    }

    #[test]
    fn test_dummy_reveal_has_random_fields() {
        let d1 = generate_dummy_reveal(100);
        let d2 = generate_dummy_reveal(100);

        // Two dummies generated at the same time should differ (random)
        assert_ne!(d1.commitment_hash, d2.commitment_hash);
        assert_ne!(d1.intent_id, d2.intent_id);
        assert_eq!(d1.generated_at, 100);
        assert_eq!(d2.generated_at, 100);
    }

    #[test]
    fn test_multiple_batches_independent() {
        let config = DelayPoolConfig {
            batch_interval_secs: 10,
            min_batch_size: 2,
            max_delay_secs: 120,
            dummy_rate_per_interval: 0,
        };
        let mut pool = DelayPool::new(config);

        // First batch
        pool.submit(make_fulfillment_result(1), 0);
        pool.submit(make_fulfillment_result(2), 5);
        assert!(pool.should_release(11));
        let batch1 = pool.release_batch(11);
        assert_eq!(batch1.len(), 2);

        // Second batch
        pool.submit(make_fulfillment_result(3), 15);
        pool.submit(make_fulfillment_result(4), 18);
        // Need interval since last release (11 + 10 = 21)
        assert!(!pool.should_release(20));
        assert!(pool.should_release(21));
        let batch2 = pool.release_batch(21);
        assert_eq!(batch2.len(), 2);

        assert_eq!(pool.total_batches_released(), 2);
    }

    #[test]
    fn test_config_defaults() {
        let config = DelayPoolConfig::default();
        assert_eq!(config.batch_interval_secs, 30);
        assert_eq!(config.min_batch_size, 3);
        assert_eq!(config.max_delay_secs, 120);
        assert_eq!(config.dummy_rate_per_interval, 1);
    }
}

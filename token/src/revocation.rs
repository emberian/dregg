//! Local revocation filter for token nonce checking.
//!
//! Uses a scalable cuckoo filter to provide O(1) revocation lookups with
//! configurable false-positive rate. The filter is designed to be populated
//! by the sidecar from `revoke.pyana.dev` (or local revocations).
//!
//! # Properties
//!
//! - **False positive rate**: configurable, default <0.1%
//! - **False negatives**: zero (revoked tokens are always caught)
//! - **Lookup time**: O(1), sub-microsecond
//! - **Storage**: ~1 byte per revoked nonce (cuckoo filter)
//!
//! Tokens with a `Revocable` caveat are checked against this filter during
//! verification. Tokens without the caveat skip the check entirely.

use rand::rngs::StdRng;
use rand::SeedableRng;
use scalable_cuckoo_filter::{ScalableCuckooFilter, ScalableCuckooFilterBuilder};
use serde::{Deserialize, Serialize};
use std::sync::Mutex;
use std::sync::atomic::{AtomicU64, Ordering};

/// Default false-positive rate for the revocation filter.
const DEFAULT_FALSE_POSITIVE_RATE: f64 = 0.001; // 0.1%

/// Default initial capacity (number of expected entries).
const DEFAULT_INITIAL_CAPACITY: usize = 1024;

/// A Send-safe RNG wrapper that implements Default (required by ScalableCuckooFilter's
/// serde deserialization, which skips the rng field and fills it via Default).
#[derive(Debug)]
struct SendRng(StdRng);

impl Default for SendRng {
    fn default() -> Self {
        Self(StdRng::from_os_rng())
    }
}

impl rand::RngCore for SendRng {
    fn next_u32(&mut self) -> u32 {
        self.0.next_u32()
    }
    fn next_u64(&mut self) -> u64 {
        self.0.next_u64()
    }
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        self.0.fill_bytes(dest)
    }
}

/// Type alias for a cuckoo filter using a Send-safe RNG.
type SendSafeFilter = ScalableCuckooFilter<str, scalable_cuckoo_filter::DefaultHasher, SendRng>;

/// Thread-safe revocation filter backed by a scalable cuckoo filter.
///
/// Provides O(1) revocation checks for token nonces. The filter can be
/// persisted to disk and restored (via serde) for sidecar restarts.
pub struct RevocationFilter {
    inner: Mutex<SendSafeFilter>,
    count: AtomicU64,
}

impl RevocationFilter {
    /// Create a new empty revocation filter with default parameters.
    pub fn new() -> Self {
        Self {
            inner: Mutex::new(
                ScalableCuckooFilterBuilder::new()
                    .initial_capacity(DEFAULT_INITIAL_CAPACITY)
                    .false_positive_probability(DEFAULT_FALSE_POSITIVE_RATE)
                    .rng(SendRng(StdRng::from_os_rng()))
                    .finish(),
            ),
            count: AtomicU64::new(0),
        }
    }

    /// Create a revocation filter with custom capacity and FPR.
    pub fn with_capacity(capacity: usize, false_positive_rate: f64) -> Self {
        Self {
            inner: Mutex::new(
                ScalableCuckooFilterBuilder::new()
                    .initial_capacity(capacity)
                    .false_positive_probability(false_positive_rate)
                    .rng(SendRng(StdRng::from_os_rng()))
                    .finish(),
            ),
            count: AtomicU64::new(0),
        }
    }

    /// Mark a token nonce as revoked.
    ///
    /// After this call, `is_revoked(nonce)` will return `true` for this nonce.
    pub fn revoke(&self, nonce: &str) {
        let mut filter = self.inner.lock().unwrap();
        filter.insert(nonce);
        self.count.fetch_add(1, Ordering::Relaxed);
    }

    /// Check whether a token nonce has been revoked.
    ///
    /// Returns `true` if the nonce is (probably) in the filter.
    /// False positive rate is controlled by the filter's FPR parameter.
    /// False negatives are impossible — if a nonce was revoked, this returns `true`.
    pub fn is_revoked(&self, nonce: &str) -> bool {
        let filter = self.inner.lock().unwrap();
        filter.contains(nonce)
    }

    /// Number of nonces that have been revoked (approximate — counts insertions).
    pub fn revoked_count(&self) -> u64 {
        self.count.load(Ordering::Relaxed)
    }

    /// Serialize the filter to bytes for persistence.
    pub fn to_bytes(&self) -> Result<Vec<u8>, rmp_serde::encode::Error> {
        let filter = self.inner.lock().unwrap();
        let snapshot = RevocationSnapshot {
            filter: filter.clone(),
            count: self.count.load(Ordering::Relaxed),
        };
        rmp_serde::to_vec(&snapshot)
    }

    /// Restore a filter from serialized bytes.
    pub fn from_bytes(data: &[u8]) -> Result<Self, rmp_serde::decode::Error> {
        let snapshot: RevocationSnapshot = rmp_serde::from_slice(data)?;
        Ok(Self {
            inner: Mutex::new(snapshot.filter),
            count: AtomicU64::new(snapshot.count),
        })
    }
}

impl Default for RevocationFilter {
    fn default() -> Self {
        Self::new()
    }
}

/// Serializable snapshot of the revocation filter state.
#[derive(Serialize, Deserialize)]
struct RevocationSnapshot {
    filter: SendSafeFilter,
    count: u64,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_filter_is_empty() {
        let filter = RevocationFilter::new();
        assert_eq!(filter.revoked_count(), 0);
        assert!(!filter.is_revoked("nonce-123"));
    }

    #[test]
    fn test_revoke_and_check() {
        let filter = RevocationFilter::new();
        filter.revoke("nonce-abc");
        assert!(filter.is_revoked("nonce-abc"));
        assert!(!filter.is_revoked("nonce-xyz"));
        assert_eq!(filter.revoked_count(), 1);
    }

    #[test]
    fn test_multiple_revocations() {
        let filter = RevocationFilter::new();
        for i in 0..100 {
            filter.revoke(&format!("nonce-{i}"));
        }
        assert_eq!(filter.revoked_count(), 100);

        // All revoked nonces should be found
        for i in 0..100 {
            assert!(filter.is_revoked(&format!("nonce-{i}")));
        }
    }

    #[test]
    fn test_serialize_deserialize_roundtrip() {
        let filter = RevocationFilter::new();
        filter.revoke("revoked-1");
        filter.revoke("revoked-2");
        filter.revoke("revoked-3");

        let bytes = filter.to_bytes().expect("serialization failed");
        let restored = RevocationFilter::from_bytes(&bytes).expect("deserialization failed");

        assert_eq!(restored.revoked_count(), 3);
        assert!(restored.is_revoked("revoked-1"));
        assert!(restored.is_revoked("revoked-2"));
        assert!(restored.is_revoked("revoked-3"));
        assert!(!restored.is_revoked("not-revoked"));
    }

    #[test]
    fn test_custom_capacity() {
        let filter = RevocationFilter::with_capacity(10_000, 0.0001);
        filter.revoke("test-nonce");
        assert!(filter.is_revoked("test-nonce"));
    }

    #[test]
    fn test_concurrent_access() {
        use std::sync::Arc;
        use std::thread;

        let filter = Arc::new(RevocationFilter::new());
        let mut handles = Vec::new();

        // Spawn writers
        for i in 0..10 {
            let f = Arc::clone(&filter);
            handles.push(thread::spawn(move || {
                for j in 0..100 {
                    f.revoke(&format!("t{i}-n{j}"));
                }
            }));
        }

        // Wait for all writers
        for h in handles {
            h.join().unwrap();
        }

        assert_eq!(filter.revoked_count(), 1000);

        // Verify all nonces are found
        for i in 0..10 {
            for j in 0..100 {
                assert!(filter.is_revoked(&format!("t{i}-n{j}")));
            }
        }
    }
}

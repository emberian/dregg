//! Operator-side configuration for a dregg-node deployment.
//!
//! # Receipts as persistence — `RetentionPolicy`
//!
//! The houyhnhnm comparison (`HOUYHNHNM-COMPARISON.md` §5.1, §8.1) names a
//! discipline dregg implicitly assumed but never declared: a federation
//! member's `WitnessedReceipt` chain is the persistence layer, and an
//! operator running a node has the *last say* on how much of that layer
//! they retain locally. Houyhnhnm's persistence-is-policy framing makes
//! the choice explicit. We adopt it here.
//!
//! Dragon's Egg's receipt chain is *the* canonical persistence stream
//! (`turn/src/turn.rs` doc header). `RetentionPolicy` declares which
//! suffix of the stream this operator commits to *serving*. Pruned
//! receipts are not lost to the federation — they live in archival
//! storage attested by [`dregg_cell::lifecycle::ArchivalAttestation`] —
//! but this operator no longer holds them in their hot tail. Queries
//! against pruned receipts must be answered with a *structured*
//! response naming the attestation that covers them, not a generic 404.
//!
//! The wire-level shape is [`dregg_wire::message::WireMessage::RequestReceipt`]
//! / [`dregg_wire::message::WireMessage::ReceiptResponse`].
//!
//! ## Default is `Forever`
//!
//! Per the *improve-don't-degrade* policy, the default is `Forever` —
//! turning on pruning is an explicit operator choice. A naive operator
//! using the default will never accidentally drop receipts they should
//! have kept.

use serde::{Deserialize, Serialize};

/// How a node operator chooses to retain receipts locally.
///
/// This is a *per-operator* declaration; it is NOT a federation-wide
/// protocol parameter. Different members of the same federation can run
/// with different retention policies. The wire protocol always carries
/// a structured "I no longer serve this; here's the attestation that
/// covers it" response so cross-member queries remain answerable.
///
/// **Invariant:** Whatever a node prunes, it MUST be able to point at an
/// [`dregg_cell::lifecycle::ArchivalAttestation`] (or equivalent
/// AttestedRoot) that covers the pruned range. The protocol cannot
/// allow "I dropped it and I don't remember." See [`Self::is_pruning`].
///
/// # Variants
///
/// - [`RetentionPolicy::Forever`] — default; never prune.
/// - [`RetentionPolicy::RollingWindow`] — prune receipts older than N
///   block-heights behind the current tip.
/// - [`RetentionPolicy::UntilArchive`] — prune receipts at heights at
///   or below a known archival attestation's `archive_end_height`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum RetentionPolicy {
    /// Never prune. The operator commits to serving the full receipt
    /// chain back to genesis.
    ///
    /// This is the *default* per `improve-don't-degrade`: a node that
    /// has not opted into pruning will not silently lose data.
    Forever,

    /// Keep only the most recent `blocks` heights of the receipt chain;
    /// older receipts may be pruned (off-loaded to archival storage).
    ///
    /// A query for a pruned receipt returns
    /// [`dregg_wire::message::ReceiptUnavailable::CoveredByAttestedRoot`].
    RollingWindow {
        /// Number of recent block-heights to retain in the hot tail.
        /// A receipt at height `h` is pruned when `tip - h >= blocks`.
        blocks: u64,
    },

    /// Keep only receipts at heights strictly *above* the named
    /// archival checkpoint. Receipts at heights ≤ `archive_height` are
    /// considered covered by the
    /// [`dregg_cell::lifecycle::ArchivalAttestation`] whose
    /// `archive_end_height` equals `archive_height`.
    UntilArchive {
        /// The `archive_end_height` of the standing archival
        /// attestation. Receipts at heights ≤ this are pruned.
        archive_height: u64,
    },
}

impl Default for RetentionPolicy {
    /// Default to [`RetentionPolicy::Forever`].
    ///
    /// Per the *improve-don't-degrade* policy, pruning is opt-in: a
    /// node started without an explicit retention configuration retains
    /// everything. Accidentally enabling pruning on a fresh deployment
    /// would *degrade* a known-good behavior, which we refuse to do.
    fn default() -> Self {
        Self::Forever
    }
}

impl RetentionPolicy {
    /// Is this policy actually pruning anything, or is it a no-op
    /// retain-everything mode?
    ///
    /// Wire responders use this to decide whether the
    /// "covered-by-attestation" path is even reachable.
    pub fn is_pruning(&self) -> bool {
        match self {
            Self::Forever => false,
            Self::RollingWindow { blocks: 0 } => false,
            Self::RollingWindow { .. } => true,
            Self::UntilArchive { .. } => true,
        }
    }

    /// Given the current tip height and a queried receipt's height,
    /// declare whether *this policy would prune* that receipt.
    ///
    /// This is the operator-side predicate that decides whether to
    /// return [`dregg_wire::message::WireMessage::ReceiptResponse`]
    /// with [`dregg_wire::message::ReceiptUnavailable::CoveredByAttestedRoot`]
    /// (when the receipt-was-archived-but-not-served) versus a real
    /// receipt body.
    ///
    /// Returns `true` when the policy *would prune* a receipt at
    /// `receipt_height`, given a current `tip_height`.
    pub fn would_prune(&self, receipt_height: u64, tip_height: u64) -> bool {
        match self {
            Self::Forever => false,
            Self::RollingWindow { blocks } => {
                if *blocks == 0 {
                    false
                } else {
                    tip_height.saturating_sub(receipt_height) >= *blocks
                }
            }
            Self::UntilArchive { archive_height } => receipt_height <= *archive_height,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn default_is_forever() {
        // Improve-don't-degrade: default MUST be Forever so a naive
        // operator never accidentally enables pruning.
        assert_eq!(RetentionPolicy::default(), RetentionPolicy::Forever);
        assert!(!RetentionPolicy::default().is_pruning());
    }

    #[test]
    fn forever_never_prunes() {
        let policy = RetentionPolicy::Forever;
        assert!(!policy.would_prune(0, 1_000_000));
        assert!(!policy.would_prune(500_000, 1_000_000));
        assert!(!policy.would_prune(1_000_000, 1_000_000));
    }

    #[test]
    fn rolling_window_prunes_old() {
        let policy = RetentionPolicy::RollingWindow { blocks: 100 };
        // tip=1000, retain heights 901..=1000 → prune anything ≤ 900
        assert!(policy.would_prune(500, 1000));
        assert!(policy.would_prune(900, 1000));
        assert!(!policy.would_prune(901, 1000));
        assert!(!policy.would_prune(1000, 1000));
    }

    #[test]
    fn rolling_window_zero_is_noop() {
        // A zero-window degenerate case is reported as non-pruning so
        // it does NOT trip the wire-level "covered by archive" path.
        let policy = RetentionPolicy::RollingWindow { blocks: 0 };
        assert!(!policy.is_pruning());
        assert!(!policy.would_prune(0, 1000));
    }

    #[test]
    fn until_archive_prunes_below() {
        let policy = RetentionPolicy::UntilArchive {
            archive_height: 500,
        };
        assert!(policy.would_prune(0, 1000));
        assert!(policy.would_prune(500, 1000));
        assert!(!policy.would_prune(501, 1000));
        assert!(!policy.would_prune(1000, 1000));
    }

    #[test]
    fn serde_roundtrip() {
        for policy in [
            RetentionPolicy::Forever,
            RetentionPolicy::RollingWindow { blocks: 7 },
            RetentionPolicy::UntilArchive { archive_height: 42 },
        ] {
            let bytes = postcard::to_stdvec(&policy).unwrap();
            let back: RetentionPolicy = postcard::from_bytes(&bytes).unwrap();
            assert_eq!(back, policy);
        }
    }
}

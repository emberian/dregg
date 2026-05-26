//! Federation receipt with BLS threshold quorum certificate.
//!
//! Implements [`DESIGN-receipts.md`] §4: a typed receipt the federation
//! produces after committing a turn, carrying a constant-size BLS aggregate
//! signature over the receipt body. The receipt is the unit of
//! cross-federation evidence; it survives federation A → federation B
//! transmission without B knowing A's committee size.
//!
//! ## Threshold property
//!
//! The receipt's [`QuorumCertificate`] is one of two flavors:
//!
//! - [`ReceiptQc::Threshold`] — a single [`ThresholdQC`] (BLS aggregate over
//!   `body_hash_blake3(body)`). Constant size, O(1) verification, **strongly
//!   preferred** for cross-federation receipts.
//! - [`ReceiptQc::Votes`] — a fallback `(voter_id, Signature)` list signed by
//!   the federation's Ed25519 keys. O(n) verification. Used in solo mode and
//!   tests where the BLS hints setup is not initialized.
//!
//! Replacing the legacy forgeable-hash "signatures" used to live at the fast
//! path layer (R-5 in `EFFECT-VM-SHAPE-A.md`) with BLS thresholds at the
//! receipt layer makes the federation receipt cryptographically sound against
//! a committee with up to `n - threshold` corrupted members: anything below
//! threshold cannot produce a valid aggregate signature.

use serde::{Deserialize, Serialize};

use crate::identity::derive_federation_id_with_epoch;
use crate::threshold::{FederationCommittee, ThresholdQC};
use crate::types::{PublicKey, Signature};
use dregg_types::{CellId, ThresholdQC as OpaqueThresholdQC};

// =============================================================================
// FederationReceiptBody
// =============================================================================

/// The body of a federation receipt — the canonical, signed content.
///
/// Mirrors [`DESIGN-receipts.md`] §4.2. The body is hashed via BLAKE3 and the
/// QC is over `body_hash_blake3(body)` (32 bytes).
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct FederationReceiptBody {
    /// BLAKE3 of the turn (must be `Turn::hash()` of the executed turn).
    pub turn_hash: [u8; 32],
    /// Block this turn was committed in.
    pub block_height: u64,
    /// Block hash (binds the receipt to the canonical block).
    pub block_hash: [u8; 32],
    /// The agent cell whose state changed.
    pub agent: CellId,
    /// Per-agent nonce.
    pub nonce: u64,
    /// Pre-state hash (BLAKE3 of canonical pre-state).
    pub pre_state_hash: [u8; 32],
    /// Post-state hash (BLAKE3 of canonical post-state).
    pub post_state_hash: [u8; 32],
    /// Effects-hash (BLAKE3 of the runtime effect sequence).
    pub effects_hash: [u8; 32],
    /// `previous_receipt_hash` in this agent's chain (binds the chain link).
    pub previous_receipt_hash: Option<[u8; 32]>,
}

impl FederationReceiptBody {
    /// Compute the canonical body hash — what the BLS QC actually signs.
    ///
    /// Domain-separated via BLAKE3 derive_key, so it cannot collide with any
    /// other dregg signing message (vote, attested root, bridge phase).
    pub fn body_hash(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("dregg-fed-receipt-body-v1");
        hasher.update(&self.turn_hash);
        hasher.update(&self.block_height.to_le_bytes());
        hasher.update(&self.block_hash);
        hasher.update(self.agent.as_bytes());
        hasher.update(&self.nonce.to_le_bytes());
        hasher.update(&self.pre_state_hash);
        hasher.update(&self.post_state_hash);
        hasher.update(&self.effects_hash);
        match self.previous_receipt_hash {
            Some(h) => {
                hasher.update(&[1u8]);
                hasher.update(&h);
            }
            None => {
                hasher.update(&[0u8]);
            }
        }
        *hasher.finalize().as_bytes()
    }
}

// =============================================================================
// ReceiptQc
// =============================================================================

/// The quorum certificate flavor carried by a [`FederationReceipt`].
///
/// Per `DESIGN-receipts.md` §4.1, the BLS `ThresholdQC` form is strongly
/// preferred for cross-federation receipts because it is constant size.
/// The `Votes` form is retained for solo mode and tests, and as a transparent
/// audit trail when an aggregator wants to publish the individual signers.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum ReceiptQc {
    /// Constant-size BLS aggregate over [`FederationReceiptBody::body_hash`].
    /// This is the production path. Stored as opaque bytes (the serialized
    /// `hints::Signature`) so callers without the verifier can pass it
    /// through without dragging in the heavy hints crate.
    Threshold(OpaqueThresholdQC),
    /// Per-voter Ed25519 fallback: signatures over the same `body_hash`,
    /// signed by each voter's federation key.
    Votes(Vec<(PublicKey, Signature)>),
}

// =============================================================================
// FederationReceipt
// =============================================================================

/// A federation-produced receipt with a (BLS or Ed25519) quorum certificate.
///
/// The QC is over [`FederationReceiptBody::body_hash`]. Verification is via
/// [`FederationReceipt::verify`] which dispatches to either the BLS path or
/// the Ed25519 path depending on the QC flavor.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct FederationReceipt {
    /// Version tag: "dregg-fed-receipt-v1".
    pub version: u32,
    /// Federation identity (BLAKE3 over the committee's static descriptor).
    pub federation_id: [u8; 32],
    /// Committee epoch (rotates with key rotations; binds receipt to a
    /// specific verifier key).
    pub committee_epoch: u64,
    /// The signed body.
    pub body: FederationReceiptBody,
    /// The quorum certificate over `body.body_hash()`.
    pub qc: ReceiptQc,
}

impl FederationReceipt {
    /// Version tag baked into the wire format.
    pub const VERSION: u32 = 1;

    /// Build a receipt carrying a BLS threshold QC.
    ///
    /// The caller is responsible for having aggregated the partial signatures
    /// via [`FederationCommittee::aggregate`] against `body.body_hash()`.
    pub fn with_threshold_qc(
        federation_id: [u8; 32],
        committee_epoch: u64,
        body: FederationReceiptBody,
        qc: &ThresholdQC,
    ) -> Self {
        Self {
            version: Self::VERSION,
            federation_id,
            committee_epoch,
            body,
            qc: ReceiptQc::Threshold(OpaqueThresholdQC(qc.to_bytes())),
        }
    }

    /// Build a receipt carrying the Ed25519 fallback.
    ///
    /// Each `(pubkey, signature)` must sign `body.body_hash()`. Used in solo
    /// mode and tests; production cross-federation receipts should use the
    /// threshold variant.
    pub fn with_vote_signatures(
        federation_id: [u8; 32],
        committee_epoch: u64,
        body: FederationReceiptBody,
        votes: Vec<(PublicKey, Signature)>,
    ) -> Self {
        Self {
            version: Self::VERSION,
            federation_id,
            committee_epoch,
            body,
            qc: ReceiptQc::Votes(votes),
        }
    }

    /// Verify this receipt.
    ///
    /// Closes finding F1 + F4 in `AUDIT-federation.md`:
    ///
    /// 1. The carried `federation_id` MUST equal
    ///    `derive_federation_id_with_epoch(known_keys, self.committee_epoch)`.
    ///    This binds receipt to (committee, epoch); a receipt tagged with one
    ///    federation but signed by another's committee is rejected.
    /// 2. The carried `committee_epoch` MUST match the caller's `expected_epoch`.
    ///    Old-epoch receipts presented under a new-epoch committee are rejected.
    /// 3. The QC (threshold or per-voter) must verify cryptographically.
    ///
    /// - For the `Threshold` flavor: requires the BLS `committee` for aggregate
    ///   verification.
    /// - For the `Votes` flavor: requires the `known_keys` slice; signatures
    ///   must be cryptographically valid over `body_hash` AND a unique-signer
    ///   count must meet `threshold`.
    pub fn verify(
        &self,
        committee: Option<&FederationCommittee>,
        known_keys: &[PublicKey],
        threshold: usize,
        expected_epoch: u64,
    ) -> bool {
        if self.version != Self::VERSION {
            return false;
        }

        // F4: epoch must match what the caller currently considers active.
        if self.committee_epoch != expected_epoch {
            return false;
        }

        // F1: federation_id must commit to the actual committee + epoch.
        // We bind to the Ed25519 `known_keys` because that's the substrate the
        // live node operates over (genesis validators). The BLS committee
        // is auxiliary; it shares the same federation, so the same id.
        let expected_id = derive_federation_id_with_epoch(known_keys, self.committee_epoch);
        if expected_id != self.federation_id {
            return false;
        }

        let body_hash = self.body.body_hash();
        match &self.qc {
            ReceiptQc::Threshold(opaque) => {
                let Some(committee) = committee else {
                    return false;
                };
                let Some(qc) = ThresholdQC::from_bytes(&opaque.0) else {
                    return false;
                };
                committee.verify(&qc, &body_hash).is_ok()
            }
            ReceiptQc::Votes(votes) => {
                if votes.len() < threshold {
                    return false;
                }
                let mut seen = std::collections::HashSet::new();
                let mut valid = 0usize;
                for (pk, sig) in votes {
                    if !known_keys.contains(pk) {
                        return false;
                    }
                    if !pk.verify(&body_hash, sig) {
                        return false;
                    }
                    if seen.insert(pk.0) {
                        valid += 1;
                    }
                }
                valid >= threshold
            }
        }
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::identity::derive_federation_id;
    use crate::threshold::generate_test_committee;
    use dregg_types::{generate_keypair, sign};
    use hints::PartialSignature;

    fn sample_body(seed: u8) -> FederationReceiptBody {
        FederationReceiptBody {
            turn_hash: [seed; 32],
            block_height: 7,
            block_hash: [seed.wrapping_add(1); 32],
            agent: CellId::from_bytes([seed.wrapping_add(2); 32]),
            nonce: 1,
            pre_state_hash: [seed.wrapping_add(3); 32],
            post_state_hash: [seed.wrapping_add(4); 32],
            effects_hash: [seed.wrapping_add(5); 32],
            previous_receipt_hash: None,
        }
    }

    #[test]
    fn body_hash_is_domain_separated() {
        // Two different bodies must hash to different values.
        let h1 = sample_body(1).body_hash();
        let h2 = sample_body(2).body_hash();
        assert_ne!(h1, h2);

        // The hash is stable for an unchanged body.
        assert_eq!(sample_body(7).body_hash(), sample_body(7).body_hash());
    }

    #[test]
    fn threshold_receipt_verifies_under_committee() {
        // 4-member committee, threshold 3. We also produce a parallel Ed25519
        // committee for the federation_id derivation (in production the same
        // genesis validators have both Ed25519 + BLS keys; here we just need
        // *some* Ed25519 set to bind the receipt's federation_id).
        let (committee, members) = generate_test_committee(4, 3).unwrap();
        let ed_keys: Vec<PublicKey> = (0..4).map(|_| generate_keypair().1).collect();
        let fed_id = derive_federation_id(&ed_keys);

        let body = sample_body(42);
        let body_hash = body.body_hash();

        // 3 of 4 members sign — meets threshold.
        let shares: Vec<(usize, PartialSignature)> = members[0..3]
            .iter()
            .map(|m| (m.index, committee.sign_share(m, &body_hash)))
            .collect();
        let qc = committee.aggregate(&shares, &body_hash).unwrap();

        let receipt = FederationReceipt::with_threshold_qc(fed_id, 0, body, &qc);

        assert!(
            receipt.verify(Some(&committee), &ed_keys, 0, 0),
            "threshold receipt must verify against its committee"
        );
    }

    #[test]
    fn threshold_receipt_rejected_when_federation_id_mismatches() {
        // F1: a receipt tagged with a different federation_id must not verify
        // even if the BLS QC is otherwise valid.
        let (committee, members) = generate_test_committee(4, 3).unwrap();
        let ed_keys: Vec<PublicKey> = (0..4).map(|_| generate_keypair().1).collect();

        let body = sample_body(11);
        let body_hash = body.body_hash();
        let shares: Vec<(usize, PartialSignature)> = members[0..3]
            .iter()
            .map(|m| (m.index, committee.sign_share(m, &body_hash)))
            .collect();
        let qc = committee.aggregate(&shares, &body_hash).unwrap();

        // Lie about federation_id: pretend it's all-zeros instead of the
        // derived value. The QC is still valid but the binding check fires.
        let bogus = FederationReceipt::with_threshold_qc([0u8; 32], 0, body, &qc);
        assert!(
            !bogus.verify(Some(&committee), &ed_keys, 0, 0),
            "receipt with wrong federation_id must be rejected (F1)"
        );
    }

    #[test]
    fn threshold_receipt_rejected_when_epoch_mismatches() {
        // F4: epoch binding must be consulted.
        let (committee, members) = generate_test_committee(4, 3).unwrap();
        let ed_keys: Vec<PublicKey> = (0..4).map(|_| generate_keypair().1).collect();
        let fed_id_e1 = derive_federation_id_with_epoch(&ed_keys, 1);

        let body = sample_body(13);
        let body_hash = body.body_hash();
        let shares: Vec<(usize, PartialSignature)> = members[0..3]
            .iter()
            .map(|m| (m.index, committee.sign_share(m, &body_hash)))
            .collect();
        let qc = committee.aggregate(&shares, &body_hash).unwrap();

        // Receipt claims epoch 1; verifier expects epoch 2 → reject.
        let receipt = FederationReceipt::with_threshold_qc(fed_id_e1, 1, body, &qc);
        assert!(
            !receipt.verify(Some(&committee), &ed_keys, 0, 2),
            "receipt with stale committee_epoch must be rejected (F4)"
        );
        // Same receipt with matching expected_epoch verifies.
        assert!(receipt.verify(Some(&committee), &ed_keys, 0, 1));
    }

    #[test]
    fn threshold_receipt_fails_under_below_threshold() {
        // 4-member committee, threshold 3. Verify that the aggregation step
        // ITSELF refuses to produce a QC when fewer than `threshold` members
        // signed: this is the soundness property of the BLS threshold scheme.
        let (committee, members) = generate_test_committee(4, 3).unwrap();
        let body = sample_body(7);
        let body_hash = body.body_hash();

        let shares: Vec<(usize, PartialSignature)> = members[0..2]
            .iter()
            .map(|m| (m.index, committee.sign_share(m, &body_hash)))
            .collect();
        let agg = committee.aggregate(&shares, &body_hash);
        assert!(
            agg.is_err(),
            "aggregation must fail when below threshold (the core threshold property)"
        );
    }

    #[test]
    fn threshold_receipt_fails_on_wrong_body() {
        // A receipt's QC over body A must not verify against a modified body.
        let (committee, members) = generate_test_committee(4, 3).unwrap();
        let ed_keys: Vec<PublicKey> = (0..4).map(|_| generate_keypair().1).collect();
        let fed_id = derive_federation_id(&ed_keys);

        let body_a = sample_body(1);
        let hash_a = body_a.body_hash();
        let shares: Vec<(usize, PartialSignature)> = members[0..3]
            .iter()
            .map(|m| (m.index, committee.sign_share(m, &hash_a)))
            .collect();
        let qc = committee.aggregate(&shares, &hash_a).unwrap();

        let body_b = sample_body(2); // different body
        let bogus_receipt = FederationReceipt::with_threshold_qc(fed_id, 0, body_b, &qc);
        assert!(
            !bogus_receipt.verify(Some(&committee), &ed_keys, 0, 0),
            "QC signed over body_a must not satisfy a receipt carrying body_b"
        );
    }

    #[test]
    fn votes_receipt_verifies_above_threshold() {
        // Ed25519 fallback: 3 federation keypairs, threshold 2.
        let kps: Vec<(_, _)> = (0..3).map(|_| generate_keypair()).collect();
        let known_keys: Vec<PublicKey> = kps.iter().map(|(_, pk)| pk.clone()).collect();
        let fed_id = derive_federation_id(&known_keys);

        let body = sample_body(9);
        let body_hash = body.body_hash();
        let votes: Vec<(PublicKey, Signature)> = kps[..2]
            .iter()
            .map(|(sk, pk)| (pk.clone(), sign(sk, &body_hash)))
            .collect();

        let receipt = FederationReceipt::with_vote_signatures(fed_id, 0, body, votes);
        assert!(receipt.verify(None, &known_keys, 2, 0));
    }

    #[test]
    fn votes_receipt_fails_when_signer_unknown() {
        let (sk1, pk1) = generate_keypair();
        let (_sk2, pk2) = generate_keypair();
        // pk2's owner did not "consent" — pretend only pk1 is in the known set.
        let known_keys = vec![pk1.clone()];
        let fed_id = derive_federation_id(&known_keys);

        let body = sample_body(3);
        let votes = vec![(pk2.clone(), sign(&sk1, &body.body_hash()))];
        let receipt = FederationReceipt::with_vote_signatures(fed_id, 0, body, votes);
        assert!(
            !receipt.verify(None, &known_keys, 1, 0),
            "signers outside known_keys must be rejected"
        );
    }

    #[test]
    fn votes_receipt_rejects_duplicate_signer() {
        let (sk, pk) = generate_keypair();
        let known_keys = vec![pk.clone()];
        let fed_id = derive_federation_id(&known_keys);

        let body = sample_body(8);
        let body_hash = body.body_hash();
        // Same key signs twice; threshold 2 must NOT be met.
        let sig = sign(&sk, &body_hash);
        let votes = vec![(pk.clone(), sig.clone()), (pk.clone(), sig)];
        let receipt = FederationReceipt::with_vote_signatures(fed_id, 0, body, votes);
        assert!(
            !receipt.verify(None, &known_keys, 2, 0),
            "duplicate-signer replay must not satisfy threshold"
        );
    }
}

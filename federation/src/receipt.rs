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

use crate::frost::MlDsaPublicKey;
use crate::identity::derive_federation_id_hybrid_with_epoch;
use crate::threshold::{FederationCommittee, ThresholdQC};
use crate::types::{PublicKey, Signature};
use dregg_types::{CellId, HybridQuorumSig, ThresholdQC as OpaqueThresholdQC};

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
    /// Pre-state ANCHOR: the AIR-bound chip 8-felt state commitment
    /// (`dregg_turn::state_commit`), packed 8 × 4 LE = 32 bytes. This was a
    /// BLAKE3 `Ledger::root()`; it is now the same Poseidon2 carrier the
    /// deployed rotated EffectVM trace publishes as `STATE_COMMIT`. The BLS
    /// threshold QC over `body_hash` therefore makes a genuine **quorum
    /// certificate over the AIR-bound commitment** rather than over a
    /// trusted-Rust Merkle root. See `dregg_turn::state_commit` for the labeled
    /// residual (the `⟺` refinement certifies the 1-felt chain, not this one;
    /// and this is a per-cell, not whole-ledger, commitment).
    pub pre_state_hash: [u8; 32],
    /// Post-state ANCHOR — the same object as [`Self::pre_state_hash`], one
    /// transition later.
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
    ///
    /// **v2:** bumped when `pre_state_hash` / `post_state_hash` became the
    /// AIR-bound chip 8-felt anchor instead of the trusted-Rust BLAKE3 ledger
    /// root. Same widths, different value and meaning — the bump keeps a v1
    /// threshold signature from ever verifying against a v2 body.
    pub fn body_hash(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("dregg-fed-receipt-body-v2");
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
    ///
    /// **PQ boundary (scoped, honest).** A BLS aggregate is a SINGLE
    /// committee-independent object with NO per-signer material, so it cannot be
    /// hybridized the per-signer way [`Self::HybridVotes`] is: there is nowhere
    /// to hang each voter's ML-DSA-65 companion. A post-quantum receipt uses the
    /// [`Self::HybridVotes`] flavor instead; the BLS path stays out of hybrid
    /// scope until a threshold-PQ aggregate (e.g. the Hermine lattice-threshold
    /// certificate in [`crate::frost::HermineHybridQC`]) is production-ready. No
    /// PQ check is faked onto this variant.
    Threshold(OpaqueThresholdQC),
    /// Per-voter Ed25519 fallback: signatures over the same `body_hash`,
    /// signed by each voter's federation key. CLASSICAL only.
    Votes(Vec<(PublicKey, Signature)>),
    /// Per-voter HYBRID (ed25519 ∧ ML-DSA-65) signatures over the same
    /// `body_hash`. Each [`HybridQuorumSig`] carries a voter's classical
    /// signature AND its post-quantum signature plus the self-contained ML-DSA
    /// public key. A signer counts toward threshold only when BOTH halves
    /// verify; a forged or missing PQ half fails the whole certificate closed
    /// (see [`verify_hybrid_quorum_sigs`]). Appended LAST so the postcard
    /// discriminants of [`Self::Threshold`]/[`Self::Votes`] — and thus every
    /// classical receipt's wire bytes — are unchanged.
    HybridVotes(Vec<HybridQuorumSig>),
}

/// Verify a hybrid quorum PINNED to the enrolled roster — the Lean
/// `hybridVerify = classical ∧ pq`, with the post-quantum key bound to genesis.
///
/// `known_keys` is the ed25519 committee and `ml_dsa_committee` is the ENROLLED
/// ML-DSA-65 roster, aligned INDEX-FOR-INDEX (element `i` of one is the same
/// member as element `i` of the other, exactly as genesis publishes them).
/// The enrolled ML-DSA keys must also be pairwise distinct: one PQ authority
/// cannot occupy multiple classical committee slots.
///
/// Accepts iff at least `threshold` DISTINCT signers each satisfy ALL of:
/// * committee membership — `pubkey ∈ known_keys` (at some index `i`);
/// * (classical) the ed25519 `signature` verifies over `message`;
/// * (PQ-key PIN) the self-carried `ml_dsa_pubkey` equals the ENROLLED key
///   `ml_dsa_committee[i]` — a signer may NOT bring its own ML-DSA key;
/// * (post-quantum) the `pq_signature` ML-DSA-65-verifies over `message` (bound
///   to [`crate::frost::HYBRID_PQ_CTX`]) under that ENROLLED key.
///
/// This is the fix for the quantum-forgery downgrade: without the PIN, an
/// adversary who breaks ed25519 for member `P` could attach its OWN fresh
/// ML-DSA keypair and a PQ signature valid under it, and BOTH halves would pass
/// (the PQ half was checked against the attacker's self-carried key). Pinning
/// the PQ key to the genesis-enrolled roster means the PQ half must verify under
/// `P`'s real ML-DSA key, which the adversary does not hold — mirroring the
/// FROST positional pin in [`crate::frost::verify_pq_quorum_half`].
///
/// FAIL-CLOSED: a roster misaligned in length (`ml_dsa_committee.len() !=
/// known_keys.len()`, which includes an EMPTY roster — hybrid not configured),
/// duplicate enrolled ML-DSA keys, any signer outside `known_keys`, any
/// signature that does not verify, a
/// self-carried ML-DSA key that differs from the enrolled one, or a missing PQ
/// half rejects the WHOLE quorum — never a silent ed25519-only downgrade.
/// `threshold == 0` (a vacuous quorum) is refused outright.
///
/// Shared by the receipt QC's [`ReceiptQc::HybridVotes`], the hybrid checkpoint
/// ([`crate::checkpoint::Checkpoint::verify_hybrid`]), and the cross-fed
/// attested-root hybrid quorum — the one place the classical ∧ pq rule lives.
pub fn verify_hybrid_quorum_sigs(
    sigs: &[HybridQuorumSig],
    message: &[u8],
    known_keys: &[PublicKey],
    ml_dsa_committee: &[MlDsaPublicKey],
    threshold: usize,
) -> bool {
    if threshold == 0 || sigs.len() < threshold {
        return false;
    }
    // The enrolled PQ roster MUST align index-for-index with the ed25519
    // committee — otherwise there is no well-defined "enrolled key for member
    // P" to pin against. A misaligned length (an EMPTY roster included) cannot
    // pin any signer, so fail closed rather than fall back to ed25519 only.
    // Distinct Ed signers cannot share one enrolled PQ authority. Check the
    // whole roster, including slots absent from this certificate's subset.
    if ml_dsa_committee.len() != known_keys.len()
        || ml_dsa_committee
            .iter()
            .enumerate()
            .any(|(i, key)| ml_dsa_committee[..i].contains(key))
    {
        return false;
    }
    // Map each committee member to its enrolled index (for the PQ-key pin).
    let index_of: std::collections::HashMap<&PublicKey, usize> =
        known_keys.iter().enumerate().map(|(i, k)| (k, i)).collect();
    let mut seen: std::collections::HashSet<[u8; 32]> = std::collections::HashSet::new();
    let mut valid = 0usize;
    for qs in sigs {
        // Committee membership — and the member's enrolled index.
        let Some(&idx) = index_of.get(&qs.pubkey) else {
            return false;
        };
        // Classical (ed25519) half.
        if !qs.pubkey.verify(message, &qs.signature) {
            return false;
        }
        // Post-quantum half — PINNED to the enrolled roster. The self-carried
        // key must be a byte-identical COPY of the enrolled key (never trusted
        // on its own), and the PQ signature is verified under the ENROLLED key.
        let enrolled = &ml_dsa_committee[idx];
        if qs.ml_dsa_pubkey.as_slice() != enrolled.0.as_slice() {
            return false;
        }
        if !enrolled.verify(message, &qs.pq_signature) {
            return false;
        }
        // Count only DISTINCT signers whose BOTH halves passed.
        if seen.insert(qs.pubkey.0) {
            valid += 1;
        }
    }
    valid >= threshold
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

    /// Build a receipt carrying the HYBRID (ed25519 ∧ ML-DSA-65) fallback.
    ///
    /// Each [`HybridQuorumSig`] must carry BOTH a valid ed25519 signature and a
    /// valid ML-DSA-65 signature (with the signer's self-contained ML-DSA public
    /// key) over `body.body_hash()`. This is the post-quantum cross-federation
    /// receipt: [`FederationReceipt::verify`] counts a signer only when both
    /// halves pass (see [`verify_hybrid_quorum_sigs`]).
    pub fn with_hybrid_vote_signatures(
        federation_id: [u8; 32],
        committee_epoch: u64,
        body: FederationReceiptBody,
        sigs: Vec<HybridQuorumSig>,
    ) -> Self {
        Self {
            version: Self::VERSION,
            federation_id,
            committee_epoch,
            body,
            qc: ReceiptQc::HybridVotes(sigs),
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
    /// - For the `HybridVotes` flavor: requires BOTH `known_keys` AND the
    ///   ENROLLED `ml_dsa_keys` roster (aligned index-for-index); each signer's
    ///   self-carried ML-DSA key must equal its enrolled key and the PQ half
    ///   must verify under that enrolled key (see [`verify_hybrid_quorum_sigs`]).
    pub fn verify(
        &self,
        committee: Option<&FederationCommittee>,
        known_keys: &[PublicKey],
        ml_dsa_keys: &[MlDsaPublicKey],
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

        // F1 + COUPLED-CORE: federation_id must commit to the actual committee +
        // epoch. The committee identity is the HYBRID id — `hybrid_id_commitment(
        // ed25519, ml_dsa)` per member — so the id commits to the enrolled ML-DSA
        // roster, not Ed25519 alone. `ml_dsa_keys` is aligned index-for-index with
        // `known_keys` (both from genesis / the live roster); when it is present
        // this derives the same hybrid id genesis wrote. An empty `ml_dsa_keys`
        // (threshold/BLS-only receipts with no PQ roster) falls back to the legacy
        // Ed25519-only id — genesis and this re-derivation MUST agree on the form.
        let expected_id =
            derive_federation_id_hybrid_with_epoch(known_keys, ml_dsa_keys, self.committee_epoch);
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
                // Membership of each signer in the known set is the only query — index it
                // once so the per-vote check is O(1) instead of a linear scan.
                let known: std::collections::HashSet<&PublicKey> = known_keys.iter().collect();
                let mut seen = std::collections::HashSet::new();
                let mut valid = 0usize;
                for (pk, sig) in votes {
                    if !known.contains(pk) {
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
            ReceiptQc::HybridVotes(sigs) => {
                // classical ∧ pq per signer, membership, PQ key pinned to the
                // enrolled roster, ≥ threshold distinct.
                verify_hybrid_quorum_sigs(sigs, &body_hash, known_keys, ml_dsa_keys, threshold)
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
    use crate::identity::{
        derive_federation_id, derive_federation_id_hybrid_with_epoch,
        derive_federation_id_with_epoch,
    };
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
            receipt.verify(Some(&committee), &ed_keys, &[], 0, 0),
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
            !bogus.verify(Some(&committee), &ed_keys, &[], 0, 0),
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
            !receipt.verify(Some(&committee), &ed_keys, &[], 0, 2),
            "receipt with stale committee_epoch must be rejected (F4)"
        );
        // Same receipt with matching expected_epoch verifies.
        assert!(receipt.verify(Some(&committee), &ed_keys, &[], 0, 1));
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
            !bogus_receipt.verify(Some(&committee), &ed_keys, &[], 0, 0),
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
        assert!(receipt.verify(None, &known_keys, &[], 2, 0));
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
            !receipt.verify(None, &known_keys, &[], 1, 0),
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
            !receipt.verify(None, &known_keys, &[], 2, 0),
            "duplicate-signer replay must not satisfy threshold"
        );
    }

    #[test]
    fn hybrid_quorum_rejects_duplicate_enrolled_pq_keys() {
        use crate::frost::MlDsaSigningKey;

        dregg_pq_testkit::install_or_panic();
        let ed = [
            dregg_types::SigningKey::from_bytes(&[0xA1; 32]),
            dregg_types::SigningKey::from_bytes(&[0xA2; 32]),
        ];
        let committee = [ed[0].public_key(), ed[1].public_key()];
        let pq = [
            MlDsaSigningKey::from_seed(&[0xA3; 32]),
            MlDsaSigningKey::from_seed(&[0xA4; 32]),
        ];
        let enrolled = [pq[0].0.clone(), pq[1].0.clone()];
        assert_ne!(committee[0], committee[1]);
        assert_ne!(enrolled[0], enrolled[1]);
        let message = sample_body(0xA5).body_hash();
        let honest: Vec<HybridQuorumSig> = (0..2)
            .map(|i| HybridQuorumSig {
                pubkey: committee[i],
                signature: sign(&ed[i], &message),
                ml_dsa_pubkey: enrolled[i].0.to_vec(),
                pq_signature: pq[i].1.sign(&message).expect("ML-DSA signs"),
            })
            .collect();
        assert!(verify_hybrid_quorum_sigs(
            &honest, &message, &committee, &enrolled, 2,
        ));

        // This is not a corrupted/missing PQ half: one actual, valid PQ
        // signature is reused under two distinct, valid classical signatures.
        let duplicated = [enrolled[0].clone(), enrolled[0].clone()];
        let reused_pq = pq[0].1.sign(&message).expect("ML-DSA signs");
        let mut aliased = honest.clone();
        for qs in &mut aliased {
            qs.ml_dsa_pubkey = duplicated[0].0.to_vec();
            qs.pq_signature = reused_pq.clone();
        }
        assert_eq!(aliased[0].pq_signature, aliased[1].pq_signature);
        for (qs, enrolled_key) in aliased.iter().zip(&duplicated) {
            assert!(qs.pubkey.verify(&message, &qs.signature));
            assert_eq!(qs.ml_dsa_pubkey.as_slice(), enrolled_key.0.as_slice());
            assert!(enrolled_key.verify(&message, &qs.pq_signature));
        }
        assert!(!verify_hybrid_quorum_sigs(
            &aliased, &message, &committee, &duplicated, 2,
        ));
        // Even a one-signer subset cannot make a duplicate enrollment valid.
        assert!(!verify_hybrid_quorum_sigs(
            &aliased[..1], &message, &committee, &duplicated, 1,
        ));
    }

    #[test]
    fn hybrid_votes_receipt_verifies_and_pq_teeth() {
        use crate::frost::MlDsaSigningKey;
        // 3 ed25519 committee keypairs + a per-member ML-DSA-65 keypair.
        let kps: Vec<(_, _)> = (0..3).map(|_| generate_keypair()).collect();
        let known_keys: Vec<PublicKey> = kps.iter().map(|(_, pk)| pk.clone()).collect();
        let pq: Vec<(_, _)> = (0..3)
            .map(|i| {
                let mut s = [0u8; 32];
                s[0] = 0x30;
                s[1] = i as u8;
                MlDsaSigningKey::from_seed(&s)
            })
            .collect();

        // The ENROLLED ML-DSA roster — aligned index-for-index with `known_keys`.
        let ml_dsa_roster: Vec<MlDsaPublicKey> = pq.iter().map(|(pk, _)| pk.clone()).collect();
        // COUPLED-CORE: the receipt's federation_id commits to the HYBRID roster,
        // so it must be derived from (known_keys, ml_dsa_roster) — the same id the
        // verifier re-derives from the enrolled roster.
        let fed_id = derive_federation_id_hybrid_with_epoch(&known_keys, &ml_dsa_roster, 0);

        let body = sample_body(9);
        let body_hash = body.body_hash();
        let make = |idxs: &[usize]| -> Vec<HybridQuorumSig> {
            idxs.iter()
                .map(|&i| HybridQuorumSig {
                    pubkey: kps[i].1.clone(),
                    signature: sign(&kps[i].0, &body_hash),
                    ml_dsa_pubkey: pq[i].0.0.to_vec(),
                    pq_signature: pq[i].1.sign(&body_hash).expect("ml-dsa sign"),
                })
                .collect()
        };

        // Honest 2-of-3 hybrid quorum verifies (BOTH halves, PQ key enrolled).
        let receipt =
            FederationReceipt::with_hybrid_vote_signatures(fed_id, 0, body.clone(), make(&[0, 1]));
        assert!(
            receipt.verify(None, &known_keys, &ml_dsa_roster, 2, 0),
            "honest hybrid receipt must verify"
        );

        // TEETH: forge the ML-DSA half, keep a VALID ed25519 half → REJECT.
        let mut forged = make(&[0, 1]);
        forged[0].pq_signature[0] ^= 0xFF;
        let bad = FederationReceipt::with_hybrid_vote_signatures(fed_id, 0, body.clone(), forged);
        assert!(
            !bad.verify(None, &known_keys, &ml_dsa_roster, 2, 0),
            "forged ML-DSA half must reject even with a valid ed25519 half"
        );

        // TEETH: missing (empty) PQ half → REJECT.
        let mut missing = make(&[0, 1]);
        missing[1].pq_signature = Vec::new();
        let bad2 = FederationReceipt::with_hybrid_vote_signatures(fed_id, 0, body.clone(), missing);
        assert!(
            !bad2.verify(None, &known_keys, &ml_dsa_roster, 2, 0),
            "missing ML-DSA half must reject"
        );

        // TEETH: a wrong-length ML-DSA pubkey → REJECT (self-carried key ≠ enrolled).
        let mut badkey = make(&[0, 1]);
        badkey[0].ml_dsa_pubkey = vec![0u8; 10];
        let bad3 = FederationReceipt::with_hybrid_vote_signatures(fed_id, 0, body.clone(), badkey);
        assert!(
            !bad3.verify(None, &known_keys, &ml_dsa_roster, 2, 0),
            "undecodable ML-DSA pubkey must reject"
        );

        // Membership: a fully-valid hybrid signer OUTSIDE the committee → REJECT.
        let (outsider_sk, outsider_pk) = generate_keypair();
        let (out_pq_pk, out_pq_sk) = MlDsaSigningKey::from_seed(&[0x99; 32]);
        let outsider = vec![HybridQuorumSig {
            pubkey: outsider_pk,
            signature: sign(&outsider_sk, &body_hash),
            ml_dsa_pubkey: out_pq_pk.0.to_vec(),
            pq_signature: out_pq_sk.sign(&body_hash).expect("ml-dsa sign"),
        }];
        let bad4 =
            FederationReceipt::with_hybrid_vote_signatures(fed_id, 0, body.clone(), outsider);
        assert!(
            !bad4.verify(None, &known_keys, &ml_dsa_roster, 1, 0),
            "non-member hybrid signer must reject"
        );
    }

    /// **THE QUANTUM-FORGERY ADVERSARIAL TEST.** This is the exact attack the
    /// enrolled-roster PIN closes: a quantum adversary breaks ed25519 for an
    /// ENROLLED member `P` (here we just use P's real ed25519 key to stand in
    /// for the forged classical half), then generates its OWN fresh ML-DSA-65
    /// keypair, signs the PQ half with it, and carries that attacker key in
    /// `ml_dsa_pubkey`. Before the fix, the PQ half was checked against the
    /// self-carried key, so BOTH halves passed. With the PIN, the self-carried
    /// key ≠ P's ENROLLED key, so the whole quorum is rejected — the ML-DSA half
    /// must verify under the genesis-enrolled key the adversary does not hold.
    #[test]
    fn quantum_forged_pq_key_is_rejected() {
        use crate::frost::MlDsaSigningKey;
        let kps: Vec<(_, _)> = (0..3).map(|_| generate_keypair()).collect();
        let known_keys: Vec<PublicKey> = kps.iter().map(|(_, pk)| pk.clone()).collect();
        // The genesis-ENROLLED ML-DSA roster (aligned with `known_keys`).
        let pq: Vec<(_, _)> = (0..3)
            .map(|i| {
                let mut s = [0u8; 32];
                s[0] = 0x40;
                s[1] = i as u8;
                MlDsaSigningKey::from_seed(&s)
            })
            .collect();
        let ml_dsa_roster: Vec<MlDsaPublicKey> = pq.iter().map(|(pk, _)| pk.clone()).collect();
        // COUPLED-CORE: federation_id commits to the hybrid roster.
        let fed_id = derive_federation_id_hybrid_with_epoch(&known_keys, &ml_dsa_roster, 0);

        let body = sample_body(21);
        let body_hash = body.body_hash();

        // The ATTACKER's fresh ML-DSA keypair for members 0 and 1 (≠ enrolled).
        let attacker0 = MlDsaSigningKey::from_seed(&[0xAA; 32]);
        let attacker1 = MlDsaSigningKey::from_seed(&[0xBB; 32]);
        let forged = vec![
            HybridQuorumSig {
                pubkey: kps[0].1.clone(),
                signature: sign(&kps[0].0, &body_hash), // "forged" ed25519 half (P's real key)
                ml_dsa_pubkey: attacker0.0.0.to_vec(),
                pq_signature: attacker0.1.sign(&body_hash).expect("ml-dsa sign"),
            },
            HybridQuorumSig {
                pubkey: kps[1].1.clone(),
                signature: sign(&kps[1].0, &body_hash),
                ml_dsa_pubkey: attacker1.0.0.to_vec(),
                pq_signature: attacker1.1.sign(&body_hash).expect("ml-dsa sign"),
            },
        ];
        // The PQ signatures verify under the ATTACKER keys, yet the quorum is
        // REJECTED because those keys are not the enrolled roster.
        let attack =
            FederationReceipt::with_hybrid_vote_signatures(fed_id, 0, body.clone(), forged);
        assert!(
            !attack.verify(None, &known_keys, &ml_dsa_roster, 2, 0),
            "a self-carried attacker ML-DSA key must be rejected (not the enrolled key)"
        );

        // HONEST path stays green: the assembler copies the ENROLLED key in.
        let honest: Vec<HybridQuorumSig> = (0..2)
            .map(|i| HybridQuorumSig {
                pubkey: kps[i].1.clone(),
                signature: sign(&kps[i].0, &body_hash),
                ml_dsa_pubkey: pq[i].0.0.to_vec(),
                pq_signature: pq[i].1.sign(&body_hash).expect("ml-dsa sign"),
            })
            .collect();
        let good = FederationReceipt::with_hybrid_vote_signatures(fed_id, 0, body, honest);
        assert!(
            good.verify(None, &known_keys, &ml_dsa_roster, 2, 0),
            "the honest enrolled-key quorum still verifies"
        );

        // NO SILENT DOWNGRADE: an empty (misaligned) enrolled roster fails closed
        // even for the honest signers.
        assert!(
            !good.verify(None, &known_keys, &[], 2, 0),
            "an unconfigured (empty) enrolled roster must fail closed, never ed25519-only"
        );
    }
}

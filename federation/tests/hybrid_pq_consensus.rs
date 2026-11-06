//! The `HybridPq` quorum surface, anchored on the LIVE types — the
//! [`dregg_federation::types`] wire values and the [`dregg_federation::frost`]
//! verifiers that real consensus (`dregg-node`'s finalization votes) rides.
//!
//! Classical half = the EXISTING ed25519 `votes` quorum (unchanged);
//! post-quantum half = per-member FIPS 204 ML-DSA-65 signatures over the SAME
//! canonical vote message. These tests cover:
//!
//! * WIRE PINS: the pre-existing `ConsensusMessage` discriminants and the
//!   `Vote` byte length are pinned byte-for-byte; the hybrid variants are
//!   APPENDED, never interleaved.
//! * HYBRID VERIFY: a hand-assembled certificate verifies via
//!   `HybridQuorumCertificate::verify_with_keys` AND via the
//!   `QuorumScheme::HybridVotes` selector over opaque bytes; a missing,
//!   forged, or slot-swapped ML-DSA signature is rejected.
//! * FAIL-CLOSED: a misaligned, incomplete, or empty PQ key table refuses to
//!   verify (never a silent classical downgrade at the hybrid seam).
//!
//! Collection-time and end-to-end finalization coverage lives on the REAL
//! consensus path: `node/src/finalization_votes.rs` (the hybrid
//! `FinalizationVoteCollector`, including its own fail-closed
//! no-configured-keys test) and the `frost.rs` `verify_hybrid_quorum` unit
//! tests.

use dregg_federation::frost::{
    MlDsaPublicKey, MlDsaSigningKey, QuorumScheme, verify_pq_quorum_half,
};
use dregg_federation::{
    ConsensusMessage, HybridQuorumCertificate, HybridVote, PublicKey, QuorumCertificate,
    SigningKey, Vote, generate_keypair, quorum_threshold, sign,
};

// =============================================================================
// DEFAULT PATH — byte-identical wire
// =============================================================================

/// Pin the postcard wire encoding of the DEFAULT path: `Vote`'s byte length
/// (proves no field was added to the vote that crosses the TCP transport) and
/// the enum discriminants of every pre-existing `ConsensusMessage` variant
/// (proves the hybrid variants were APPENDED, not interleaved).
#[test]
fn default_wire_bytes_are_pinned() {
    let (sk, _pk) = generate_keypair();
    let vote_message = QuorumCertificate::vote_message(&[7u8; 32], 1, 1);
    let vote = Vote {
        block_hash: [7u8; 32],
        height: 1,
        view: 1,
        voter: 0,
        signature: sign(&sk, &vote_message),
    };

    // Vote: 32 (block_hash array) + 1 (height varint) + 1 (view varint)
    //     + 1 (voter varint) + 65 (Signature: len-prefixed 64-byte seq)
    //     = 100 bytes, exactly as before the hybrid landed. A new field
    //     would change this length.
    let vote_bytes = postcard::to_stdvec(&vote).unwrap();
    assert_eq!(vote_bytes.len(), 100, "Vote wire shape must be unchanged");

    // ConsensusMessage discriminants (postcard varint tags): the historical
    // variants keep their positions; the hybrid ones are strictly after.
    let vote_msg = postcard::to_stdvec(&ConsensusMessage::VoteMsg(vote.clone())).unwrap();
    assert_eq!(vote_msg[0], 1, "VoteMsg discriminant must stay 1");
    assert_eq!(
        &vote_msg[1..],
        &vote_bytes[..],
        "VoteMsg payload must be exactly the unchanged Vote bytes"
    );
    let get_root = postcard::to_stdvec(&ConsensusMessage::GetAttestedRoot).unwrap();
    assert_eq!(
        get_root,
        vec![4],
        "GetAttestedRoot discriminant must stay 4"
    );
    let view_change = postcard::to_stdvec(&ConsensusMessage::ViewChange(
        dregg_federation::ViewChangeMessage {
            new_view: 2,
            height: 1,
            voter: 0,
            signature: sign(&sk, b"vc"),
        },
    ))
    .unwrap();
    assert_eq!(view_change[0], 6, "ViewChange discriminant must stay 6");

    // The appended hybrid variants sit AFTER every historical one.
    let hybrid_vote = postcard::to_stdvec(&ConsensusMessage::HybridVoteMsg(HybridVote {
        vote,
        pq_signature: vec![0u8; 4],
    }))
    .unwrap();
    assert_eq!(hybrid_vote[0], 7, "HybridVoteMsg is appended at 7");
}

// =============================================================================
// Fixture: a hand-assembled hybrid committee + certificate (no simulator —
// exactly the values the real vote path signs and the real verifiers check).
// =============================================================================

struct HybridCommittee {
    ed_keys: Vec<SigningKey>,
    members: Vec<PublicKey>,
    pq_keys: Vec<MlDsaSigningKey>,
    pq_members: Vec<MlDsaPublicKey>,
    threshold: usize,
}

fn hybrid_committee(n: usize) -> HybridCommittee {
    // An INTEGRATION test compiles `dregg-federation` without `cfg(test)`, so the install inside
    // `frost::MlDsaSigningKey::from_seed` is inert here and this binary died as a bare SIGABRT the
    // moment it derived its first ML-DSA key. `hybrid_committee` is the one gateway this file
    // uses into the PQ path, so the install belongs here.
    dregg_pq_testkit::install_or_panic();
    let keypairs: Vec<_> = (0..n).map(|_| generate_keypair()).collect();
    let members: Vec<_> = keypairs.iter().map(|(_, pk)| *pk).collect();
    let ed_keys: Vec<_> = keypairs.into_iter().map(|(sk, _)| sk).collect();
    let (pq_members, pq_keys): (Vec<_>, Vec<_>) = (0..n)
        .map(|i| {
            let mut seed = [0u8; 32];
            seed[0] = 0x42;
            seed[1] = i as u8;
            MlDsaSigningKey::from_seed(&seed)
        })
        .unzip();
    HybridCommittee {
        ed_keys,
        members,
        pq_keys,
        pq_members,
        threshold: quorum_threshold(n),
    }
}

impl HybridCommittee {
    /// Assemble the certificate a leader would emit after collecting hybrid
    /// votes from `signers`: each signer signs the SAME canonical vote message
    /// with ed25519 (the classical half) and ML-DSA-65 (the PQ half).
    fn assemble_qc(
        &self,
        block_hash: [u8; 32],
        height: u64,
        view: u64,
        signers: &[usize],
    ) -> HybridQuorumCertificate {
        let message = QuorumCertificate::vote_message(&block_hash, height, view);
        let votes: Vec<_> = signers
            .iter()
            .map(|&i| (i, sign(&self.ed_keys[i], &message)))
            .collect();
        let pq_sigs: Vec<_> = signers
            .iter()
            .map(|&i| (i, self.pq_keys[i].sign(&message).expect("ML-DSA signs")))
            .collect();
        HybridQuorumCertificate {
            qc: QuorumCertificate {
                block_hash,
                height,
                view,
                aggregate_qc: None,
                votes,
                threshold: self.threshold,
            },
            pq_sigs,
        }
    }

    fn scheme(&self) -> QuorumScheme<'_> {
        QuorumScheme::HybridVotes {
            members: &self.members,
            ml_dsa_pubkeys: &self.pq_members,
        }
    }
}

// =============================================================================
// HYBRID ENABLED — verifies, round-trips, rejects forgery
// =============================================================================

#[test]
fn hybrid_qc_verifies_both_halves_and_round_trips() {
    let committee = hybrid_committee(4);
    let hqc = committee.assemble_qc([7u8; 32], 1, 1, &[0, 1, 2]);
    assert!(hqc.pq_sigs.len() >= committee.threshold);
    assert_eq!(hqc.pq_sigs.len(), hqc.qc.votes.len());

    // Full hybrid verification: classical ∧ pq.
    assert!(hqc.verify_with_keys(&committee.members, &committee.pq_members));

    // The PQ half alone also verifies via the factored frost verifier.
    let message = QuorumCertificate::vote_message(&hqc.qc.block_hash, hqc.qc.height, hqc.qc.view);
    assert!(verify_pq_quorum_half(
        &committee.pq_members,
        &message,
        &hqc.pq_sigs,
        committee.threshold,
    ));

    // …and via the scheme selector over the opaque-bytes seam.
    let opaque = hqc.to_bytes();
    let scheme = committee.scheme();
    assert!(scheme.verify_opaque_qc(&opaque, &message));
    assert!(!scheme.verify_opaque_qc(&opaque, b"some other message"));

    // Round trip through the opaque bytes.
    let hqc2 = HybridQuorumCertificate::from_bytes(&opaque).unwrap();
    assert!(hqc2.verify_with_keys(&committee.members, &committee.pq_members));

    // The classical projection is exactly today's QC and still verifies on
    // today's path.
    assert!(hqc.qc.verify_with_keys(&committee.members));
}

#[test]
fn hybrid_missing_or_forged_ml_dsa_sig_is_rejected_at_verification() {
    let committee = hybrid_committee(4);
    let hqc = committee.assemble_qc([9u8; 32], 2, 1, &[0, 1, 3]);
    let members = &committee.members;
    let pq = &committee.pq_members;
    assert!(hqc.verify_with_keys(members, pq));

    // FORGED: one flipped byte in one ML-DSA signature.
    let mut forged = hqc.clone();
    forged.pq_sigs[1].1[100] ^= 0x01;
    assert!(!forged.verify_with_keys(members, pq));

    // MISSING: dropping one PQ signature breaks the voter↔signer binding
    // (and, below threshold, the count too).
    let mut missing = hqc.clone();
    missing.pq_sigs.pop();
    assert!(!missing.verify_with_keys(members, pq));

    // SUBSTITUTED: a signature moved to another member's slot.
    let mut swapped = hqc.clone();
    let (i0, s0) = swapped.pq_sigs[0].clone();
    let (i1, s1) = swapped.pq_sigs[1].clone();
    swapped.pq_sigs[0] = (i0, s1);
    swapped.pq_sigs[1] = (i1, s0);
    assert!(!swapped.verify_with_keys(members, pq));

    // The selector rejects all of them too.
    let message = QuorumCertificate::vote_message(&hqc.qc.block_hash, hqc.qc.height, hqc.qc.view);
    let scheme = committee.scheme();
    for bad in [&forged, &missing, &swapped] {
        assert!(!scheme.verify_opaque_qc(&bad.to_bytes(), &message));
    }
}

// =============================================================================
// FAIL-CLOSED — a bad PQ key table refuses to verify
// =============================================================================

/// A hybrid committee whose PQ key table is misaligned with its member table
/// is NOT a hybrid committee: verification refuses outright — never a silent
/// downgrade to classical-only. (Construction-time refusal lives on the real
/// path: `dregg-node`'s finalization-vote collector takes a per-member PQ
/// key table and counts nothing without it.)
#[test]
fn misaligned_or_incomplete_pq_key_table_fails_closed() {
    let committee = hybrid_committee(4);
    // Include the LAST member so a truncated key table leaves a voter keyless.
    let hqc = committee.assemble_qc([3u8; 32], 1, 1, &[0, 1, 3]);
    let message = QuorumCertificate::vote_message(&hqc.qc.block_hash, hqc.qc.height, hqc.qc.view);
    assert!(hqc.verify_with_keys(&committee.members, &committee.pq_members));

    // 4 members, 3 PQ keys: voter 3 has no key at its position — refused.
    let truncated = &committee.pq_members[..3];
    assert!(!hqc.verify_with_keys(&committee.members, truncated));
    let scheme = QuorumScheme::HybridVotes {
        members: &committee.members,
        ml_dsa_pubkeys: truncated,
    };
    assert!(!scheme.verify_opaque_qc(&hqc.to_bytes(), &message));

    // Empty PQ key table: refused (the classical half alone is NOT a quorum
    // at the hybrid seam, even though it still verifies as a classical QC).
    assert!(!hqc.verify_with_keys(&committee.members, &[]));
    assert!(hqc.qc.verify_with_keys(&committee.members));

    // Misaligned: two keys swapped out of position — every signature now
    // verifies against the WRONG member's key, refused.
    let mut permuted = committee.pq_members.clone();
    permuted.swap(0, 1);
    assert!(!hqc.verify_with_keys(&committee.members, &permuted));

    // The factored PQ-half verifier is the seam enforcing all of this.
    assert!(!verify_pq_quorum_half(
        truncated,
        &message,
        &hqc.pq_sigs,
        committee.threshold,
    ));
}

// =============================================================================
// DISTINCT ENROLLED ROSTER — a duplicated ML-DSA roster cannot inflate a quorum
// =============================================================================

/// A roster that ENROLS THE SAME ML-DSA KEY at two positions cannot inflate the
/// LIVE-consensus hybrid quorum: the shared PQ-half verifier refuses a roster
/// that repeats a key, even when the reused signature sits at two DISTINCT
/// positions under two distinct, valid classical halves. Mirrors the
/// distinct-roster contract `receipt::verify_hybrid_quorum_sigs` enforces
/// (task/4721) at the `frost::verify_pq_quorum_half` seam this path routes
/// through. Without it, one holder of that PQ key fills a 2-of-2 PQ half.
#[test]
fn duplicate_enrolled_pq_roster_is_refused() {
    let committee = hybrid_committee(2);
    let message = QuorumCertificate::vote_message(&[5u8; 32], 1, 1);
    // One REAL ML-DSA signature (member 0's key), reused under BOTH members.
    let reused = committee.pq_keys[0].sign(&message).expect("ML-DSA signs");
    let hqc = HybridQuorumCertificate {
        qc: QuorumCertificate {
            block_hash: [5u8; 32],
            height: 1,
            view: 1,
            aggregate_qc: None,
            votes: vec![
                (0, sign(&committee.ed_keys[0], &message)),
                (1, sign(&committee.ed_keys[1], &message)),
            ],
            threshold: 2,
        },
        pq_sigs: vec![(0, reused.clone()), (1, reused)],
    };
    // The classical half is genuine and passes on its own…
    assert!(hqc.qc.verify_with_keys(&committee.members));
    // …and the PQ half, with the honest distinct roster, verifies.
    let honest_pq = vec![
        (0, committee.pq_keys[0].sign(&message).unwrap()),
        (1, committee.pq_keys[1].sign(&message).unwrap()),
    ];
    let honest = HybridQuorumCertificate {
        pq_sigs: honest_pq,
        ..hqc.clone()
    };
    assert!(honest.verify_with_keys(&committee.members, &committee.pq_members));

    // A roster that enrols member 0's key at BOTH positions.
    let mut dup_roster = committee.pq_members.clone();
    dup_roster[1] = dup_roster[0].clone();

    // The hybrid certificate must REFUSE: one enrolled PQ authority is not two.
    assert!(!hqc.verify_with_keys(&committee.members, &dup_roster));
    // …and via the opaque-bytes LIVE-consensus seam.
    let scheme = QuorumScheme::HybridVotes {
        members: &committee.members,
        ml_dsa_pubkeys: &dup_roster,
    };
    assert!(!scheme.verify_opaque_qc(&hqc.to_bytes(), &message));
    // The factored PQ-half verifier is where the refusal lives.
    assert!(!verify_pq_quorum_half(&dup_roster, &message, &hqc.pq_sigs, 2));
}

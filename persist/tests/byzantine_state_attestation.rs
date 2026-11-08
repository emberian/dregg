//! LIVE-BYZANTINE Attack 5b forge — the SERVED state attestation carries no
//! committee binding (the store now does — Fix B landed — but the API wire is
//! still count-only).
//!
//! The deployed cross-node committee quorum (`node::finalization_votes`, v2)
//! binds `(block_id, merkle_root)` and, since Fix B, is back-filled into the
//! persisted root's `finalization_quorum`
//! (`blocklace_sync.rs::backfill_finalization_quorums`). But
//! `GET /api/federation/roots` (`api.rs::get_federation_roots`) still surfaces
//! a root as `{ merkle_root, signatures: quorum_signatures.len() }` — a COUNT,
//! with no committee verification and no `finalization_quorum` exposure.
//!
//! This forge shows a single Byzantine node can present TWO conflicting state
//! roots for the SAME finalized block, each passing the count-only gate the API
//! serves, so a light client trusting that surface cannot arbitrate them — the
//! committee certificate over the state is not in the SERVED artifact. (It also
//! models the pre-back-fill TRAILING-HEAD shape: a root persisted before its
//! votes converge legitimately carries an empty `finalization_quorum`.)
//!
//! It ALSO pins the Fix-B discriminator itself: `finalization_quorum` +
//! `verify_finalization_quorum` (the committee's v2 finalization votes OVER
//! `(block_id, merkle_root)`) is crypto-bound, not a count — the property the
//! served surface must expose (and a light client verify) to close Attack 5b.
//!
//! The negative arms below are built so each is RED for the check it NAMES, not
//! green-by-over-determination: each varies exactly ONE half of an otherwise
//! PERFECT quorum entry, so deleting the check that arm names flips it to
//! ACCEPT (a clean assertion failure). That requires real ed25519 AND ML-DSA-65
//! material in-file, derived exactly as the live commit path does — see
//! `Committee`. It still never touches the actively-edited `persist/src/tests.rs`.
//!
//! See `docs/audit/LIVE-BYZANTINE.md` Attack 5b (and Attack 3 — the same weld).

use dregg_federation::frost::MlDsaSigningKey;
use dregg_persist::StoredAttestedRoot;
use dregg_persist::federation::{
    FederationId, MlDsaPublicKey, PublicKey, QuorumSignature, Signature,
};
use dregg_types::{SigningKey, sign};

// The ML-DSA-65 derivations and verifications in this file go through `dregg-pq`,
// which ABORTS the process — `process::abort`, not a panic — with no verified core
// installed; see `dregg-pq-testkit`'s crate docs. `dregg-federation`'s own
// `#[cfg(test)] install_or_panic()` is INERT here: that crate is compiled as a
// DEPENDENCY of this test binary, so `cfg(test)` is false in its `src/`. Every
// other PQ-touching integration test installs the cores at process start; this
// file did not, so any mutation that let an arm reach `enrolled.verify` — or the
// fixture's own keygen — died with a bare SIGABRT (fab exit 101) instead of
// failing an assertion. That is a crash, not proof (task/4869).
dregg_pq_testkit::install_at_process_start!();

/// A full-mode attested root as the deployed commit path FIRST persists it
/// (the trailing-head shape, before `backfill_finalization_quorums` attaches the
/// converged votes): bound to a blocklace block + height, carrying a single
/// (producer-local) `quorum_signatures` entry, threshold 3 (the N3 committee
/// shape), and an EMPTY `finalization_quorum` — also exactly the shape a forger
/// who holds no committee keys can mint.
fn full_mode_root(
    block_id: [u8; 32],
    merkle_root: [u8; 32],
    producer: PublicKey,
) -> StoredAttestedRoot {
    StoredAttestedRoot {
        merkle_root,
        note_tree_root: None,
        nullifier_set_root: None,
        height: 1,
        timestamp: 1_700_000_000,
        blocklace_block_id: Some(block_id),
        finality_round: Some(1),
        // Full mode pushes ONLY the local signature (1 < threshold 3).
        quorum_signatures: vec![(producer, Signature([0x01; 64]))],
        threshold_qc: None,
        threshold: 3,
        federation_id: FederationId::PLACEHOLDER,
        receipt_stream_root: None,
        // Empty at first persist (the quorum trails over gossip; Fix B
        // back-fills it) — and empty forever on a forged root.
        finalization_quorum: Vec::new(),
    }
}

/// A placeholder ENROLLED ML-DSA roster aligned with a `len`-member committee.
/// Used only where the rejection is expected to fire on the COUNT (an empty /
/// sub-threshold quorum, which returns before any roster index is read); a
/// length-aligned roster ensures those arms exercise the real pinned path
/// rather than short-circuiting on a roster-length mismatch.
///
/// The keys are DISTINCT per index (one byte of `i` repeated), NOT `[0u8; 1952]`
/// repeated: a duplicated roster now trips `verify_finalization_quorum`'s own
/// pairwise-distinct roster guard (task/4854) and would short-circuit an arm
/// before the check it names.
fn junk_ml_dsa_roster(len: usize) -> Vec<MlDsaPublicKey> {
    (0..len).map(|i| MlDsaPublicKey([i as u8; 1952])).collect()
}

/// A 3-member committee + its genesis-ENROLLED ML-DSA-65 roster, aligned
/// index-for-index, plus the finalized `(block_id, merkle_root)` the votes bind.
///
/// Derived exactly as the live commit path (and as `persist/src/tests.rs`):
/// `SigningKey::from_bytes(&[s; 32])` and `MlDsaSigningKey::from_seed(&[s; 32])`.
/// The ML-DSA *secrets* are kept so an arm below can mint an entry whose PQ half
/// is GENUINE and then vary exactly ONE other half — which is what lets an arm
/// be RED for the check it names rather than green because some OTHER check also
/// rejects the entry (task/4870).
struct Committee {
    sks: Vec<SigningKey>,
    keys: Vec<PublicKey>,
    pqs: Vec<(MlDsaPublicKey, MlDsaSigningKey)>,
    roster: Vec<MlDsaPublicKey>,
    block_id: [u8; 32],
    merkle_root: [u8; 32],
}

impl Committee {
    fn fixture() -> Self {
        let sks: Vec<SigningKey> = (1u8..=3)
            .map(|s| SigningKey::from_bytes(&[s; 32]))
            .collect();
        let keys: Vec<PublicKey> = sks.iter().map(|k| k.public_key()).collect();
        let pqs: Vec<(MlDsaPublicKey, MlDsaSigningKey)> = (1u8..=3)
            .map(|s| MlDsaSigningKey::from_seed(&[s; 32]))
            .collect();
        let roster: Vec<MlDsaPublicKey> = pqs.iter().map(|(pk, _)| pk.clone()).collect();
        Self {
            sks,
            keys,
            pqs,
            roster,
            block_id: [0xCD; 32],
            merkle_root: [0xAA; 32],
        }
    }

    fn vote_msg(&self) -> Vec<u8> {
        dregg_types::finalization_vote_signing_message(&self.block_id, &self.merkle_root, None)
    }

    /// Member `i`'s honest HYBRID vote over `msg`: a genuine ed25519 half AND a
    /// genuine ML-DSA-65 half under member `i`'s ENROLLED key.
    fn vote(&self, i: usize, msg: &[u8]) -> QuorumSignature {
        QuorumSignature {
            voter: self.keys[i],
            signature: sign(&self.sks[i], msg),
            ml_dsa_pubkey: self.pqs[i].0.0.to_vec(),
            pq_signature: self.pqs[i].1.sign(msg).expect("ml-dsa signing"),
        }
    }

    /// A root whose `finalization_quorum` is `quorum` (threshold 3, the N3 shape).
    fn root_with(&self, quorum: Vec<QuorumSignature>) -> StoredAttestedRoot {
        StoredAttestedRoot {
            finalization_quorum: quorum,
            ..full_mode_root(self.block_id, self.merkle_root, self.keys[0])
        }
    }
}

/// A single Byzantine node signs two CONFLICTING state roots for the SAME
/// finalized block (same `blocklace_block_id`, same height, different
/// `merkle_root`). Both pass the count-only gate the API serves, and neither
/// carries a committee finalization quorum — so nothing in the served artifact
/// lets a light client tell the honest root from the forged one.
#[test]
fn byzantine_conflicting_state_roots_both_pass_count_only_gate() {
    let byz = PublicKey([0xBB; 32]);
    let block_id = [0xCD; 32];

    let honest = full_mode_root(block_id, [0xAA; 32], byz);
    let forged = full_mode_root(block_id, [0x00; 32], byz);

    // Same finalized block, CONFLICTING state.
    assert_eq!(honest.blocklace_block_id, forged.blocklace_block_id);
    assert_eq!(honest.height, forged.height);
    assert_ne!(honest.merkle_root, forged.merkle_root);

    // (1) The count-only gate the API's `signatures:` field reflects: a single
    // self-signature meets `is_structurally_complete()` only when threshold <= 1.
    // At the N3 threshold (3) a full-mode root is NOT structurally complete — the
    // count is 1. So a count-trusting consumer sees `signatures: 1` for BOTH
    // conflicting roots and has no committee evidence either way.
    assert_eq!(honest.quorum_signatures.len(), 1);
    assert_eq!(forged.quorum_signatures.len(), 1);
    assert!(!honest.is_structurally_complete());
    assert!(!forged.is_structurally_complete());

    // A Byzantine node CAN also declare threshold 1 (a self-federation) to make
    // its forged root `is_structurally_complete()` — the count gate cannot stop it.
    let forged_solo = StoredAttestedRoot {
        threshold: 1,
        ..forged.clone()
    };
    assert!(
        forged_solo.is_structurally_complete(),
        "count-only completeness cannot distinguish a forged solo-threshold root"
    );

    // (2) THE SERVED GAP: neither of these roots carries a committee finalization
    // quorum over its state (trailing-head / forged shape), and the API surfaces
    // nothing that would distinguish a back-filled root anyway — a light client
    // reading the served artifact has NO committee certificate binding
    // `merkle_root`.
    assert!(!honest.has_finalization_quorum());
    assert!(!forged.has_finalization_quorum());

    // An EMPTY quorum is refused by the count guard (`0 < threshold 3`) before any
    // roster index is read — the roster here only keeps that refusal off a
    // roster-length mismatch.
    let committee = vec![PublicKey([1; 32]), PublicKey([2; 32]), PublicKey([3; 32])];
    let ml_dsa_committee = junk_ml_dsa_roster(committee.len());
    assert!(
        !honest.verify_finalization_quorum(&committee, &ml_dsa_committee),
        "an empty finalization_quorum cannot certify state (nothing to verify)"
    );
    assert!(!forged.verify_finalization_quorum(&committee, &ml_dsa_committee));
}

/// Pin the Fix-B gate's SOUNDNESS: `verify_finalization_quorum` is crypto-bound,
/// not a count — a Byzantine node cannot forge a state quorum by stuffing
/// `finalization_quorum` with junk signatures or non-committee keys. This is the
/// property the served root must eventually carry to close Attack 5b/3.
///
/// Every negative arm varies exactly ONE half of an otherwise-PERFECT quorum, so
/// the rejection is attributable to the check that arm NAMES (and deleting that
/// check flips the arm to ACCEPT — the mutation proofs recorded on task/4869 and
/// task/4870). An all-junk quorum would be rejected by whichever check runs
/// first and would pin none of them.
#[test]
fn finalization_quorum_rejects_forged_and_noncommittee_signatures() {
    let c = Committee::fixture();
    let msg = c.vote_msg();

    // POSITIVE CONTROL — the honest 3-of-3 hybrid quorum verifies. This is also
    // the arm that genuinely EXERCISES the PQ half: all three entries reach
    // `enrolled.verify` and must return true for it to be green.
    let honest: Vec<QuorumSignature> = (0..3).map(|i| c.vote(i, &msg)).collect();
    assert!(
        c.root_with(honest)
            .verify_finalization_quorum(&c.keys, &c.roster),
        "the honest 3-of-3 hybrid quorum must verify — the positive control the \
         negative arms below are read against"
    );

    // ARM — the CLASSICAL half is load-bearing, not decorative (task/4869).
    // Every PQ half is GENUINE (a real ML-DSA-65 signature under the enrolled key
    // it is pinned to); only the ed25519 halves are FORGED (genuine signatures
    // over a DIFFERENT root). Membership, the enrolled-PQ pin, the count and
    // distinctness all pass, so classical verification is the SOLE gate: delete
    // it and this arm ACCEPTS.
    let wrong_msg = dregg_types::finalization_vote_signing_message(&c.block_id, &[0x00; 32], None);
    let forged: Vec<QuorumSignature> = (0..3)
        .map(|i| QuorumSignature {
            signature: sign(&c.sks[i], &wrong_msg),
            ..c.vote(i, &msg)
        })
        .collect();
    assert!(
        !c.root_with(forged)
            .verify_finalization_quorum(&c.keys, &c.roster),
        "a FORGED ed25519 half must not certify even when the PQ half is genuine — \
         the gate verifies Ed25519, it does not count entries"
    );

    // ARM — MEMBERSHIP (task/4870). Three signers NOT in the committee, each with
    // a GENUINE ed25519 half (their own keys) and a GENUINE PQ half under the
    // enrolled key at the position they would be mapped to. Every other check
    // passes, so committee membership is the SOLE gate: neutralise it (map an
    // unknown voter to index 0) and this arm ACCEPTS.
    //
    // An outsider carrying its OWN ML-DSA key would instead be refused by the
    // enrolled-PQ PIN — the arm would then pin the pin, not membership. Giving the
    // outsider the enrolled key's PQ material is the strictly stronger attack:
    // even a perfectly-formed quorum of non-members must not count.
    let outsiders: Vec<SigningKey> = (9u8..=11)
        .map(|s| SigningKey::from_bytes(&[s; 32]))
        .collect();
    let sybil: Vec<QuorumSignature> = outsiders
        .iter()
        .map(|sk| QuorumSignature {
            voter: sk.public_key(),
            signature: sign(sk, &msg),
            ml_dsa_pubkey: c.roster[0].0.to_vec(),
            pq_signature: c.pqs[0].1.sign(&msg).expect("ml-dsa signing"),
        })
        .collect();
    assert!(
        !c.root_with(sybil)
            .verify_finalization_quorum(&c.keys, &c.roster),
        "non-committee signers cannot form a finalization quorum (Sybil rejected) \
         — even when their ed25519 and PQ halves are both genuine"
    );

    // ARM — the POST-QUANTUM half is load-bearing (task/4869). Every ed25519 half
    // is genuine and in the committee; ONE PQ half is corrupted. Delete the
    // enrolled-key PQ verification and this arm ACCEPTS — no silent downgrade to
    // an ed25519-only quorum.
    let mut pq_corrupt: Vec<QuorumSignature> = (0..3).map(|i| c.vote(i, &msg)).collect();
    pq_corrupt[1].pq_signature[0] ^= 0xFF;
    assert!(
        !c.root_with(pq_corrupt)
            .verify_finalization_quorum(&c.keys, &c.roster),
        "a corrupted ML-DSA half must refuse the quorum even though every ed25519 \
         half still verifies (classical ∧ pq)"
    );

    // ARM — a sub-threshold count is refused. It fires on the `len < threshold`
    // guard (and would also fail the final distinct-count bar), so it does NOT
    // isolate either one; it asserts the count floor only.
    let short = vec![c.vote(0, &msg)];
    assert!(
        !c.root_with(short)
            .verify_finalization_quorum(&c.keys, &c.roster),
        "a sub-threshold count is refused regardless of validity"
    );
}

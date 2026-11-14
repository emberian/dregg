//! **What a [`TurnAnchorV1`] refuses.** Each test breaks exactly ONE link of the custody chain
//! the module documents and pins the NAMED error, so a future edit that widens the chain has to
//! come here and delete a refusal rather than quietly stop checking.
//!
//! The completeness control (`an_honest_anchor_verifies`) runs first in spirit: without it every
//! refusal below could be a fixture that never verified in the first place.

use dregg_cell::CellId;
use dregg_federation::turn_anchor::{
    AnchorCommittee, TURN_ANCHOR_PROTOCOL_V1, TurnAnchorError, TurnAnchorV1,
};
use dregg_turn::TurnReceipt;
use dregg_types::{
    AttestedRoot, FederationId, PublicKey, SigningKey, merkle_root_of_receipt_hashes, sign,
};

const FEDERATION: FederationId = FederationId([0x5F; 32]);
const BLOCK_ID: [u8; 32] = [0x81; 32];
const HEIGHT: u64 = 42;

fn signer(seed: u8) -> (SigningKey, PublicKey) {
    let sk = SigningKey::from_bytes(&[seed; 32]);
    let pk = sk.public_key();
    (sk, pk)
}

fn receipt_for(turn_hash: [u8; 32]) -> TurnReceipt {
    TurnReceipt {
        turn_hash,
        pre_state_hash: [0x11; 32],
        post_state_hash: [0x22; 32],
        agent: CellId::from_bytes([0xA1; 32]),
        federation_id: FEDERATION.0,
        ..Default::default()
    }
}

/// Build an anchor whose attestation is signed by `signers` — the shape the node's
/// `/api/turn/{hash}/anchor` produces.
fn anchor_signed_by(turn_hash: [u8; 32], signers: &[(SigningKey, PublicKey)]) -> TurnAnchorV1 {
    let receipt = receipt_for(turn_hash);
    let mut attested = AttestedRoot {
        merkle_root: [0x33; 32],
        note_tree_root: None,
        nullifier_set_root: None,
        height: HEIGHT,
        timestamp: 1_800_000_000,
        blocklace_block_id: Some(BLOCK_ID),
        finality_round: Some(7),
        quorum_signatures: Vec::new(),
        threshold_qc: None,
        threshold: signers.len().max(1),
        federation_id: FEDERATION,
        receipt_stream_root: Some(merkle_root_of_receipt_hashes(&[receipt.receipt_hash()])),
        hybrid_quorum: Vec::new(),
    };
    let message = attested.signing_message();
    for (sk, pk) in signers {
        attested.quorum_signatures.push((*pk, sign(sk, &message)));
    }
    TurnAnchorV1 {
        protocol: TURN_ANCHOR_PROTOCOL_V1.to_string(),
        turn_hash,
        receipt,
        height: HEIGHT,
        block_id: BLOCK_ID,
        attested,
        served_committee: AnchorCommittee::default(),
    }
}

fn committee_of(signers: &[(SigningKey, PublicKey)], threshold: usize) -> AnchorCommittee {
    AnchorCommittee {
        ed25519: signers.iter().map(|(_, pk)| *pk).collect(),
        ml_dsa: Vec::new(),
        threshold,
        federation_id: FEDERATION,
    }
}

/// **COMPLETENESS.** An honest anchor, judged against the committee that signed it, verifies —
/// and hands back the turn hash a proof re-verifier should use.
#[test]
fn an_honest_anchor_verifies_and_yields_the_turn_hash() {
    let turn_hash = [0xAB; 32];
    let s = vec![signer(1)];
    let anchor = anchor_signed_by(turn_hash, &s);

    let verified = anchor
        .verify(&committee_of(&s, 1))
        .expect("an honest anchor must verify");

    assert_eq!(verified.turn_hash, turn_hash);
    assert_eq!(verified.height, HEIGHT);
    assert_eq!(verified.block_id, BLOCK_ID);
    assert_eq!(verified.receipt_quorum_signers, 1);
    assert_eq!(verified.receipt_hash, anchor.receipt.receipt_hash());
    // The 8-felt pair rides along, REPORTED. It is not the proof's — see
    // `turn/tests/receipt_state_commit_is_not_the_proof_state_commit.rs`.
    assert_eq!(verified.receipt_pre_state_commit, [0x11; 32]);
    assert_eq!(verified.receipt_post_state_commit, [0x22; 32]);
    // The hybrid vote quorum is absent in this fixture, and its absence never gates.
    assert!(!verified.position_quorum_met);
}

/// **THE SUBSTITUTION THE WHOLE TYPE EXISTS TO CATCH.** An anchor that claims turn A while
/// carrying turn B's receipt is refused by NAME, before anything derived from the receipt is
/// computed — so the failure says "wrong turn", not "stream mismatch".
#[test]
fn a_receipt_for_another_turn_is_refused_by_name() {
    let s = vec![signer(1)];
    let mut anchor = anchor_signed_by([0xAA; 32], &s);
    anchor.receipt = receipt_for([0xBB; 32]);

    match anchor.verify(&committee_of(&s, 1)) {
        Err(TurnAnchorError::ReceiptIsForAnotherTurn {
            anchor: a,
            receipt: r,
        }) => {
            assert_eq!(a, [0xAA; 32]);
            assert_eq!(r, [0xBB; 32]);
        }
        other => panic!("expected ReceiptIsForAnotherTurn, got {other:?}"),
    }
}

/// A receipt that does not hash into the attestation's signed `receipt_stream_root` is refused —
/// this is the link that makes the committee's signature reach the turn at all.
#[test]
fn a_receipt_outside_the_attested_stream_is_refused() {
    let turn_hash = [0xAB; 32];
    let s = vec![signer(1)];
    let mut anchor = anchor_signed_by(turn_hash, &s);
    // Mutate a receipt field that `receipt_hash()` absorbs but the anchor's own turn-hash check
    // does not: the stream root must then disagree.
    anchor.receipt.effects_hash = [0x99; 32];

    match anchor.verify(&committee_of(&s, 1)) {
        Err(TurnAnchorError::ReceiptNotInAttestedStream { receipt_hash, .. }) => {
            assert_eq!(receipt_hash, anchor.receipt.receipt_hash());
        }
        other => panic!("expected ReceiptNotInAttestedStream, got {other:?}"),
    }
}

/// A legacy attestation with no `receipt_stream_root` binds no receipt at all, so no signature
/// over it reaches any turn. Refused rather than accepted as "the signature checked out".
#[test]
fn an_attestation_binding_no_receipt_stream_is_refused() {
    let s = vec![signer(1)];
    let mut anchor = anchor_signed_by([0xAB; 32], &s);
    anchor.attested.receipt_stream_root = None;
    // Re-sign so the failure is about the missing binding, not a stale signature.
    let message = anchor.attested.signing_message();
    anchor.attested.quorum_signatures = vec![(s[0].1, sign(&s[0].0, &message))];

    assert!(matches!(
        anchor.verify(&committee_of(&s, 1)),
        Err(TurnAnchorError::AttestationBindsNoReceiptStream)
    ));
}

/// ⚑ **THE REFUSAL THAT SEPARATES "THE COMMITTEE SAID SO" FROM "THE NODE SAID SO".**
///
/// On the live path `AttestedRoot::quorum_signatures` receives exactly one push — the local
/// node's. A committee larger than 1 therefore cannot reach threshold on that leg alone, and
/// with NO assembled vote quorum on the root the anchor must refuse rather than report a
/// caveat. This is the state a threshold-2 federation is in before its committee's votes
/// converge; it is what v4 supplies the missing quorum for, and it must keep refusing until
/// that quorum actually exists. `node/tests/committee_signature_covers_a_per_turn_value.rs`
/// drives the accepted side through the real `VoteCollector`.
#[test]
fn a_sub_threshold_receipt_quorum_is_refused_not_caveated() {
    let turn_hash = [0xAB; 32];
    let one = signer(1);
    let two = signer(2);
    // Signed by ONE member; the committee has two and demands two.
    let anchor = anchor_signed_by(turn_hash, std::slice::from_ref(&one));
    let committee = committee_of(&[one, two], 2);

    match anchor.verify(&committee) {
        Err(TurnAnchorError::ReceiptQuorumNotMet {
            signers,
            attestation_signers,
            vote_signers,
            threshold,
        }) => {
            assert_eq!((signers, threshold), (1, 2));
            assert_eq!(
                (attestation_signers, vote_signers),
                (1, 0),
                "the one signer is the node's own attestation signature; the committee's vote \
                 quorum has not assembled"
            );
        }
        other => panic!("expected ReceiptQuorumNotMet, got {other:?}"),
    }
}

/// A signature from outside the caller's roster is not a committee signature, however valid.
#[test]
fn a_non_member_signature_does_not_count_toward_the_quorum() {
    let turn_hash = [0xAB; 32];
    let stranger = signer(9);
    let anchor = anchor_signed_by(turn_hash, std::slice::from_ref(&stranger));
    // The caller's roster names somebody else entirely.
    let committee = committee_of(&[signer(1)], 1);

    assert!(matches!(
        anchor.verify(&committee),
        Err(TurnAnchorError::ReceiptQuorumNotMet {
            signers: 0,
            threshold: 1,
            ..
        })
    ));
}

/// Duplicating one member's valid signature does not manufacture a quorum — signers are counted
/// DISTINCT, the same rule `StoredAttestedRoot::verify_signatures` applies.
#[test]
fn a_duplicated_signature_does_not_manufacture_a_quorum() {
    let turn_hash = [0xAB; 32];
    let one = signer(1);
    let two = signer(2);
    let mut anchor = anchor_signed_by(turn_hash, std::slice::from_ref(&one));
    let dup = anchor.attested.quorum_signatures[0];
    anchor.attested.quorum_signatures.push(dup);

    assert!(matches!(
        anchor.verify(&committee_of(&[one, two], 2)),
        Err(TurnAnchorError::ReceiptQuorumNotMet {
            signers: 1,
            threshold: 2,
            ..
        })
    ));
}

/// A roster is a trust root only for its own federation.
#[test]
fn an_anchor_from_another_federation_is_refused() {
    let s = vec![signer(1)];
    let anchor = anchor_signed_by([0xAB; 32], &s);
    let mut committee = committee_of(&s, 1);
    committee.federation_id = FederationId([0x11; 32]);

    assert!(matches!(
        anchor.verify(&committee),
        Err(TurnAnchorError::FederationMismatch { .. })
    ));
}

/// An anchor pointing at a different chain position than its attestation is refused.
#[test]
fn a_chain_position_that_disagrees_with_the_attestation_is_refused() {
    let s = vec![signer(1)];
    let mut anchor = anchor_signed_by([0xAB; 32], &s);
    anchor.height = HEIGHT + 1;

    assert!(matches!(
        anchor.verify(&committee_of(&s, 1)),
        Err(TurnAnchorError::ChainPositionMismatch { .. })
    ));

    let mut anchor = anchor_signed_by([0xAB; 32], &s);
    anchor.block_id = [0xEE; 32];
    assert!(matches!(
        anchor.verify(&committee_of(&s, 1)),
        Err(TurnAnchorError::ChainPositionMismatch { .. })
    ));
}

/// A vacuous committee is not an authority: an empty roster or a zero threshold refuses outright
/// rather than accepting on zero signatures.
#[test]
fn a_vacuous_committee_is_not_an_authority() {
    let s = vec![signer(1)];
    let anchor = anchor_signed_by([0xAB; 32], &s);

    assert!(matches!(
        anchor.verify(&committee_of(&s, 0)),
        Err(TurnAnchorError::NoCommittee { threshold: 0, .. })
    ));
    assert!(matches!(
        anchor.verify(&committee_of(&[], 1)),
        Err(TurnAnchorError::NoCommittee { members: 0, .. })
    ));
}

/// An unrecognised protocol tag refuses rather than being interpreted as v1.
#[test]
fn an_unknown_protocol_tag_is_refused() {
    let s = vec![signer(1)];
    let mut anchor = anchor_signed_by([0xAB; 32], &s);
    anchor.protocol = "DTA2".to_string();

    assert!(matches!(
        anchor.verify(&committee_of(&s, 1)),
        Err(TurnAnchorError::UnknownProtocol(_))
    ));
}

/// The anchor survives the wire it is actually served over (postcard hex), byte-for-byte, and
/// verifies on the far side. A shape that only verifies in-process is not an anchor.
#[test]
fn the_anchor_round_trips_the_wire_and_still_verifies() {
    let turn_hash = [0xAB; 32];
    let s = vec![signer(1)];
    let anchor = anchor_signed_by(turn_hash, &s);

    let bytes = postcard::to_stdvec(&anchor).expect("encode");
    let decoded: TurnAnchorV1 = postcard::from_bytes(&bytes).expect("decode");
    let verified = decoded
        .verify(&committee_of(&s, 1))
        .expect("a wire round-trip must not change the verdict");
    assert_eq!(verified.turn_hash, turn_hash);
}

#[test]
fn coordination_hint_never_bypasses_committee_authentication() {
    let signers = vec![signer(1)];
    let anchor = anchor_signed_by([0xAB; 32], &signers);
    let bytes = postcard::to_stdvec(&anchor).unwrap();
    let mut json = serde_json::to_value(&anchor).unwrap();
    json["proof_status"] = serde_json::json!("not_required");
    let mut decoded: TurnAnchorV1 = serde_json::from_value(json).unwrap();
    assert_eq!(postcard::to_stdvec(&decoded).unwrap(), bytes);
    assert!(decoded.verify(&committee_of(&signers, 1)).is_ok());
    decoded.attested.quorum_signatures.clear();
    assert!(
        decoded.verify(&committee_of(&signers, 1)).is_err(),
        "an exempt policy hint must never replace committee signatures"
    );
}

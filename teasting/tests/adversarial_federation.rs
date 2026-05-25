//! Adversarial federation tests — equivocation, BLS share withholding,
//! threshold near-miss, forked-blocklace prefix differentiation.
//!
//! Per AUDIT-federation.md §10 (adversarial tests *missing*),
//! AUDIT-blocklace-consensus.md §7 ("not tested" subset), and
//! AUDIT-morpheus-federation-blocklace-phase3a.md the running node has
//! tests for *single-node misbehavior* but lacks:
//!
//!   - **Equivocating federation**: same federation signs two
//!     contradictory `AttestedRoot`s at the same height — a verifier
//!     must detect this.
//!   - **BLS share withhold**: `t-1` of `n` shares submitted (one
//!     short of threshold) — aggregation must fail.
//!   - **Threshold near-miss with tampered share**: `t` shares but one
//!     has a corrupted MAC — aggregation must fail.
//!   - **Forked blocklace prefix**: the future AttestedRoot v3 must
//!     bind `(federation_id, block_id)` so two attestations on forked
//!     prefixes are distinguishable (AUDIT-federation.md F3).
//!
//! Many tests are `#[ignore]`d on AttestedRoot v3 / federation-id ↔
//! committee binding (AUDIT-federation.md F1/F3). The BLS share
//! withhold + threshold near-miss tests are exercisable today against
//! `pyana_federation::threshold::FederationCommittee`.

use pyana_federation::threshold::{ThresholdError, generate_test_committee};

// ===========================================================================
// BLS share withhold: t-1 of n must fail aggregation
// ===========================================================================

/// Per AUDIT-federation.md §10 "Adversarial tests missing" — confirm
/// that supplying `threshold - 1` shares to the aggregator produces an
/// error (not a silently-accepted aggregate). Threshold = 4 of 4.
#[test]
fn bls_t_minus_one_of_n_aggregation_rejects() {
    let n = 4;
    let threshold = 4;
    let (committee, members) = generate_test_committee(n, threshold).expect("committee");

    let message = b"adversarial-test-message-v1";

    // Collect ONLY t-1 = 3 shares.
    let shares: Vec<_> = members
        .iter()
        .take((threshold - 1) as usize)
        .map(|m| committee.sign_share(m, message))
        .collect();

    let result = committee.aggregate(&shares, message);
    assert!(
        result.is_err(),
        "aggregating fewer than threshold shares must fail; got {result:?}"
    );
}

/// Same test, but n=7, t=5; submit t-1=4 shares, ensure rejection.
#[test]
fn bls_t_minus_one_of_n_aggregation_rejects_medium_committee() {
    let n = 7;
    let threshold = 5;
    let (committee, members) = generate_test_committee(n, threshold).expect("committee");

    let message = b"medium-committee-near-miss";
    let shares: Vec<_> = members
        .iter()
        .take((threshold - 1) as usize)
        .map(|m| committee.sign_share(m, message))
        .collect();

    let result = committee.aggregate(&shares, message);
    assert!(
        result.is_err(),
        "n=7 t=5: aggregating 4 shares (one short of threshold) must fail; got {result:?}"
    );
}

// ===========================================================================
// Threshold near-miss with tampered share: t shares but one has wrong
// message
// ===========================================================================

/// Per AUDIT-federation.md §10 — t shares present, but one is signed
/// over a DIFFERENT message. The aggregate verification must fail.
#[test]
fn bls_threshold_met_but_one_share_signed_over_wrong_message_rejects() {
    let n = 4;
    let threshold = 3;
    let (committee, members) = generate_test_committee(n, threshold).expect("committee");

    let canonical_message = b"canonical-checkpoint-payload-v1";
    let attacker_message = b"alternate-checkpoint-payload";

    // Three shares, but member[2] signs over a different message.
    let s0 = committee.sign_share(&members[0], canonical_message);
    let s1 = committee.sign_share(&members[1], canonical_message);
    let s2_bad = committee.sign_share(&members[2], attacker_message);

    let shares = vec![s0, s1, s2_bad];
    let qc_result = committee.aggregate(&shares, canonical_message);

    // Either aggregation fails outright, OR aggregation succeeds but
    // verification against `canonical_message` fails — either way the
    // canonical-message attestation must not be accepted.
    match qc_result {
        Err(_) => { /* expected: aggregation failed */ }
        Ok(qc) => {
            let verify = committee.verify(&qc, canonical_message);
            assert!(
                verify.is_err(),
                "aggregate over mismatched messages must NOT verify against the canonical message"
            );
        }
    }
}

// ===========================================================================
// Solo committee edge cases (AUDIT-federation.md §10 "Threshold-edge n=1,2")
// ===========================================================================

#[test]
#[ignore = "blocked on `hints` crate accepting domain_size < 2: per AUDIT-federation.md §10 / F6, n=1 may hit the power-of-2 dummy padding edge case. Document the expected behavior here."]
fn bls_n_equals_1_threshold_1_edge_case() {
    let _ = generate_test_committee(1, 1);
    panic!("blocked");
}

#[test]
#[ignore = "blocked on `hints` crate dummy-padding semantics for n=2: AUDIT-federation.md §10"]
fn bls_n_equals_2_threshold_2_edge_case() {
    let _ = generate_test_committee(2, 2);
    panic!("blocked");
}

// ===========================================================================
// Aggregate verification — wrong message after success
// ===========================================================================

#[test]
fn bls_aggregate_does_not_verify_against_different_message() {
    let n = 4;
    let threshold = 3;
    let (committee, members) = generate_test_committee(n, threshold).expect("committee");
    let msg = b"verify-message-v1";
    let other = b"verify-message-v2";

    let shares: Vec<_> = members
        .iter()
        .take(threshold as usize)
        .map(|m| committee.sign_share(m, msg))
        .collect();
    let qc = committee.aggregate(&shares, msg).expect("aggregate ok");

    assert!(committee.verify(&qc, msg).is_ok(), "ok against signed msg");
    let result = committee.verify(&qc, other);
    assert!(
        result.is_err(),
        "QC must not verify against a different message; got {result:?}"
    );
}

// ===========================================================================
// Equivocating federation: same federation signs two contradictory
// AttestedRoots at the same height — verifier must detect
// ===========================================================================

#[test]
#[ignore = "blocked on AttestedRoot v3 binding (AUDIT-federation.md F3): until `blocklace_block_id` + `finality_round` are bound in AttestedRoot::signing_message, two attested roots at the same height with different merkle_root are 'just two different attestations' — a fork-detection layer is needed to catch the contradiction. This test asserts an equivocating-federation detector exists."]
fn equivocating_federation_two_roots_same_height_detected() {
    panic!("blocked");
}

#[test]
#[ignore = "blocked on AttestedRoot v3 binding: AttestedRoot must include `blocklace_block_id` so two attestations at the same height referencing different finality positions are distinguishable forks (AUDIT-federation.md F3)"]
fn attested_root_v3_binds_blocklace_block_id() {
    panic!("blocked");
}

#[test]
#[ignore = "blocked on AttestedRoot v3 binding: signing_message MUST include federation_id (AUDIT-federation.md F1) — without this, a verifier holding committees for two federations could match the wrong committee against a forwarded root"]
fn attested_root_signing_message_binds_federation_id() {
    panic!("blocked");
}

// ===========================================================================
// Forked-blocklace prefix differentiation
// ===========================================================================

#[test]
#[ignore = "blocked on blocklace-AttestedRoot composition (AUDIT-blocklace-consensus.md gap D, AUDIT-federation.md F3): two blocklace prefixes of equal length finalized by tau on different histories must produce distinguishable AttestedRoots — the AttestedRoot must commit to the blocklace's notion of finality (block_id + tau_index), not just `height: u64`"]
fn forked_blocklace_prefixes_produce_distinct_attested_roots() {
    panic!("blocked");
}

// ===========================================================================
// FederationReceipt: forged-tag attack (AUDIT-federation.md F1/F2/F4)
// ===========================================================================

#[test]
#[ignore = "blocked on `federation_id ↔ committee` registry (AUDIT-federation.md F1): a malicious peer takes a valid FederationReceipt from federation A, rewrites the `federation_id` field to B's, presents to a verifier that looks up the committee by `federation_id`. The verifier must use B's committee to verify and reject."]
fn federation_receipt_with_tampered_federation_id_rejected_by_registry_lookup() {
    panic!("blocked");
}

#[test]
#[ignore = "blocked on committee_epoch enforcement (AUDIT-federation.md F4): a stale receipt signed under epoch-N committee, presented in epoch-N+1 after key rotation, must be rejected by the verifier"]
fn federation_receipt_with_stale_committee_epoch_rejected() {
    panic!("blocked");
}

// ===========================================================================
// Equivocation handling discrepancy (AUDIT-blocklace-consensus.md gap B)
// ===========================================================================

#[test]
#[ignore = "blocked on unified equivocation detector (AUDIT-blocklace-consensus.md gap B): the finality-layer (seq-based) and ordering-layer (round-based) equivocation rules disagree on whether a Byzantine node bumping seq on every fork is an equivocator. This test asserts both rules fire on the same Byzantine pattern."]
fn byzantine_seq_increment_across_fork_detected_by_both_rules() {
    panic!("blocked");
}

#[test]
#[ignore = "blocked on merge tip removal (AUDIT-blocklace-consensus.md gap C): when a delta merge surfaces an equivocator, the offending creator's tip must be removed from `tips` so downstream consumers (dissemination, multi-group block creation) see a consistent state. Today `merge()` updates `equivocators` but not `tips`."]
fn merge_with_equivocator_removes_their_tip() {
    panic!("blocked");
}

// ===========================================================================
// Liveness: federation below threshold
// ===========================================================================

#[test]
#[ignore = "blocked on auto-demote-to-solo on partition (AUDIT-federation.md F8): when more than (n - threshold) members are unreachable, the federation must EITHER halt finality (preferred) OR transition to FederationMode::Solo for degraded mode — and the transition must be observable to verifiers"]
fn federation_below_threshold_halts_or_demotes() {
    panic!("blocked");
}

// ===========================================================================
// Cross-cutting: AttestedRoot replay across federations
// ===========================================================================

#[test]
#[ignore = "blocked on AttestedRoot v3 federation_id binding: an AttestedRoot signed for federation F1 must not be accepted by a verifier configured for federation F2, even if F2's committee bytes accidentally verify the BLS aggregate (which they shouldn't, but defense-in-depth)"]
fn attested_root_signed_for_f1_not_accepted_at_f2() {
    panic!("blocked");
}

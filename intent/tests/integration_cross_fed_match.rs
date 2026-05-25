//! Integration test: cross-federation ring detection via CrossFederationSolver.
//!
//! Verifies:
//! - Single-federation rings are detected and correctly labeled
//! - Multi-federation rings are detected and `is_cross_federation()` returns true
//! - The `distinct_federations()` set is correct
//! - A ring where all participants are from the same federation is NOT cross-fed
//! - `CrossFederationSolver::solve_cross_fed_only` filters correctly

use pyana_federation::{FederationId, KnownFederations};
use pyana_intent::cross_fed::{CrossFedRingTrade, CrossFederationSolver, FederatedIntentNode};
use pyana_intent::solver::{ExchangeSpec, IntentNode, RingSolver};
use pyana_intent::CommitmentId;

// ============================================================================
// Helpers
// ============================================================================

fn fed(seed: u8) -> FederationId {
    FederationId([seed; 32])
}

fn intent_node(id_seed: u8, offer: u8, want: u8, expiry: u64) -> IntentNode {
    let mut intent_id = [0u8; 32];
    intent_id[0] = id_seed;
    IntentNode {
        intent_id,
        exchange: ExchangeSpec {
            offer_asset: [offer; 32],
            offer_amount: 100,
            want_asset: [want; 32],
            want_min_amount: 90,
            min_rate: None,
            max_rate: None,
        },
        creator: CommitmentId([id_seed; 32]),
        expiry,
    }
}

fn federated(federation: FederationId, node: IntentNode) -> FederatedIntentNode {
    FederatedIntentNode { federation, node }
}

fn make_known() -> KnownFederations {
    KnownFederations::new()
}

// ============================================================================
// CrossFedRingTrade property tests (no solver needed)
// ============================================================================

#[test]
fn single_fed_ring_is_not_cross_federation() {
    let f = fed(0xAA);
    let ring = CrossFedRingTrade {
        ring: pyana_intent::solver::RingTrade {
            participants: vec![[0x01; 32], [0x02; 32]],
            settlements: vec![],
            score: 1.0,
        },
        federations: vec![f, f],
    };
    assert!(!ring.is_cross_federation());
    assert_eq!(ring.distinct_federations().len(), 1);
}

#[test]
fn two_fed_ring_is_cross_federation() {
    let f1 = fed(0x11);
    let f2 = fed(0x22);
    let ring = CrossFedRingTrade {
        ring: pyana_intent::solver::RingTrade {
            participants: vec![[0x01; 32], [0x02; 32]],
            settlements: vec![],
            score: 2.5,
        },
        federations: vec![f1, f2],
    };
    assert!(ring.is_cross_federation());
    let distinct = ring.distinct_federations();
    assert_eq!(distinct.len(), 2);
    assert!(distinct.contains(&f1));
    assert!(distinct.contains(&f2));
}

#[test]
fn three_leg_two_fed_ring_distinct_count() {
    let f1 = fed(0x33);
    let f2 = fed(0x44);
    let ring = CrossFedRingTrade {
        ring: pyana_intent::solver::RingTrade {
            participants: vec![[0x01; 32], [0x02; 32], [0x03; 32]],
            settlements: vec![],
            score: 3.0,
        },
        federations: vec![f1, f2, f1],
    };
    assert!(ring.is_cross_federation());
    assert_eq!(ring.distinct_federations().len(), 2);
}

#[test]
fn empty_federation_list_not_cross_fed() {
    let ring = CrossFedRingTrade {
        ring: pyana_intent::solver::RingTrade {
            participants: vec![],
            settlements: vec![],
            score: 0.0,
        },
        federations: vec![],
    };
    assert!(!ring.is_cross_federation());
    assert_eq!(ring.distinct_federations().len(), 0);
}

// ============================================================================
// CrossFederationSolver tests
// ============================================================================

#[test]
fn cross_fed_solver_finds_two_party_ring_across_feds() {
    // A (fed 0xAA) offers asset [0x01] for [0x02]
    // B (fed 0xBB) offers asset [0x02] for [0x01]
    // => mutual swap ring exists and spans two federations
    let f_aa = fed(0xAA);
    let f_bb = fed(0xBB);

    let node_a = intent_node(0x01, 0x01, 0x02, 9999);
    let node_b = intent_node(0x02, 0x02, 0x01, 9999);

    let pool = vec![federated(f_aa, node_a), federated(f_bb, node_b)];

    let known = make_known();
    let solver = CrossFederationSolver::new(RingSolver::new(5), &known);
    let rings = solver.solve(&pool, 0);

    let cross_rings: Vec<_> = rings.iter().filter(|r| r.is_cross_federation()).collect();
    assert!(
        !cross_rings.is_empty(),
        "mutual swap across two feds must yield at least one cross-federation ring"
    );

    let r = &cross_rings[0];
    let distinct = r.distinct_federations();
    assert_eq!(distinct.len(), 2);
    assert!(distinct.contains(&f_aa));
    assert!(distinct.contains(&f_bb));
}

#[test]
fn cross_fed_solver_no_ring_for_incompatible_intents() {
    // Both offer [0x01] for [0x02] — no swap is possible.
    let f_aa = fed(0xAA);
    let f_bb = fed(0xBB);

    let node_a = intent_node(0x01, 0x01, 0x02, 9999);
    let node_b = intent_node(0x02, 0x01, 0x02, 9999); // same direction as A

    let pool = vec![federated(f_aa, node_a), federated(f_bb, node_b)];

    let known = make_known();
    let solver = CrossFederationSolver::new(RingSolver::new(5), &known);
    let rings = solver.solve(&pool, 0);

    let cross_rings: Vec<_> = rings.iter().filter(|r| r.is_cross_federation()).collect();
    assert!(
        cross_rings.is_empty(),
        "incompatible intents must not yield a cross-federation ring"
    );
}

#[test]
fn cross_fed_solver_handles_expired_intents() {
    // node_a is already expired (expiry < now); only node_b is live.
    // With only one live intent there can be no ring.
    let f = fed(0xCC);
    let node_a = intent_node(0x10, 0x01, 0x02, 5); // expiry 5, now = 100
    let node_b = intent_node(0x11, 0x02, 0x01, 9999);

    let pool = vec![federated(f, node_a), federated(f, node_b)];

    let known = make_known();
    let solver = CrossFederationSolver::new(RingSolver::new(5), &known);
    let rings = solver.solve(&pool, 100); // now = 100 > expiry of node_a
    assert!(rings.is_empty(), "expired intent must not participate in any ring");
}

#[test]
fn solve_cross_fed_only_filters_intra_fed_rings() {
    // Two intra-fed pairs on the same federation — rings exist but are not cross-fed.
    let f = fed(0xDD);
    let node_a = intent_node(0x20, 0x01, 0x02, 9999);
    let node_b = intent_node(0x21, 0x02, 0x01, 9999);

    let pool = vec![federated(f, node_a), federated(f, node_b)];

    let known = make_known();
    let solver = CrossFederationSolver::new(RingSolver::new(5), &known);

    // solve returns rings; solve_cross_fed_only filters to none.
    let all = solver.solve(&pool, 0);
    let cross_only = solver.solve_cross_fed_only(&pool, 0);

    // all should have the intra-fed ring.
    assert!(!all.is_empty(), "intra-fed mutual swap must be detected");
    // cross_only should be empty (same fed on both sides).
    assert!(
        cross_only.is_empty(),
        "solve_cross_fed_only must exclude intra-federation rings"
    );
}

//! DFA routing integration tests: governed route tables, classification, and amendment.
//!
//! Tests the full lifecycle of DFA-governed message routing:
//! - Compile route patterns into a DFA table
//! - Classify messages and verify correct dispatch
//! - Governance: propose new routes, update atomically (compare-and-swap)
//! - Verify classification changes after route amendment
//! - Revocation: remove a route, messages get Drop classification

use pyana_captp::FederationId;
use pyana_teasting::federation::quick_federation;
use pyana_types::CellId;
use pyana_wire::dfa_router::{
    DispatchDecision, GovernanceProof, GovernedRouter, RouteTarget, RouteUpdateError, Router,
    compile_routes, dispatch_path,
};

// =============================================================================
// Helpers
// =============================================================================

fn cell_id(byte: u8) -> CellId {
    CellId([byte; 32])
}

fn fed_id(byte: u8) -> FederationId {
    FederationId([byte; 32])
}

// =============================================================================
// Test 1: Federation starts with a route table compiled from patterns
// =============================================================================

/// Compile route patterns into a DFA table and verify it has the expected
/// structure (non-zero states, non-empty accept map, deterministic commitment).
#[test]
fn test_compile_route_table() {
    let _harness = quick_federation();

    let table = compile_routes(&[
        ("/cells/stablecoin/*", RouteTarget::Cell(cell_id(0x01))),
        ("/cells/oracle/*", RouteTarget::Cell(cell_id(0x02))),
        ("/intents/*", RouteTarget::Handler("intent_pool".into())),
        ("/admin/*", RouteTarget::Handler("admin".into())),
        ("/federated/*", RouteTarget::Federation(fed_id(0x42))),
    ]);

    // Table should have meaningful states.
    assert!(
        table.num_states > 5,
        "Should have at least one state per route prefix"
    );
    assert_eq!(table.accept_map.len(), 5, "Should have 5 accept states");

    // Commitment is non-zero and deterministic.
    assert_ne!(table.commitment, [0u8; 32]);

    // Compiling again gives the same commitment.
    let table2 = compile_routes(&[
        ("/cells/stablecoin/*", RouteTarget::Cell(cell_id(0x01))),
        ("/cells/oracle/*", RouteTarget::Cell(cell_id(0x02))),
        ("/intents/*", RouteTarget::Handler("intent_pool".into())),
        ("/admin/*", RouteTarget::Handler("admin".into())),
        ("/federated/*", RouteTarget::Federation(fed_id(0x42))),
    ]);
    assert_eq!(table.commitment, table2.commitment);
}

// =============================================================================
// Test 2: Messages classified by DFA, routed to correct handlers
// =============================================================================

/// Verify that wire messages are correctly classified by running the DFA over
/// their byte content, dispatching to the appropriate target.
#[test]
fn test_classify_messages_to_correct_handlers() {
    let _harness = quick_federation();

    let table = compile_routes(&[
        ("/cells/stablecoin/*", RouteTarget::Cell(cell_id(0x01))),
        ("/cells/oracle/*", RouteTarget::Cell(cell_id(0x02))),
        ("/intents/*", RouteTarget::Handler("intent_pool".into())),
        ("/admin/*", RouteTarget::Handler("admin".into())),
        ("/federated/*", RouteTarget::Federation(fed_id(0x42))),
    ]);
    let router = Router::new(table);

    // Stablecoin cell messages.
    assert_eq!(
        router.classify_path(b"/cells/stablecoin/transfer"),
        Some(&RouteTarget::Cell(cell_id(0x01)))
    );
    assert_eq!(
        router.classify_path(b"/cells/stablecoin/balance"),
        Some(&RouteTarget::Cell(cell_id(0x01)))
    );

    // Oracle cell messages.
    assert_eq!(
        router.classify_path(b"/cells/oracle/price_feed"),
        Some(&RouteTarget::Cell(cell_id(0x02)))
    );

    // Intent pool messages.
    assert_eq!(
        router.classify_path(b"/intents/submit_swap"),
        Some(&RouteTarget::Handler("intent_pool".into()))
    );

    // Admin messages.
    assert_eq!(
        router.classify_path(b"/admin/status"),
        Some(&RouteTarget::Handler("admin".into()))
    );

    // Federated messages.
    assert_eq!(
        router.classify_path(b"/federated/sync"),
        Some(&RouteTarget::Federation(fed_id(0x42)))
    );

    // Unknown path: not classified.
    assert_eq!(router.classify_path(b"/unknown/path"), None);
    assert_eq!(router.classify_path(b"/cells/unknown/x"), None);
}

// =============================================================================
// Test 3: Governance - propose new routes -> vote -> threshold met -> routes updated
// =============================================================================

/// Governance flow: update the route table atomically using a compare-and-swap
/// proof that references the current commitment.
#[test]
fn test_governance_route_update() {
    let _harness = quick_federation();

    // Initial routes.
    let initial_table = compile_routes(&[
        ("/cells/stablecoin/*", RouteTarget::Cell(cell_id(0x01))),
        ("/intents/*", RouteTarget::Handler("intent_pool".into())),
    ]);
    let initial_commitment = initial_table.commitment;
    let mut governed = GovernedRouter::new(initial_table);

    // Verify initial classification.
    assert_eq!(
        governed.classify_path(b"/cells/stablecoin/transfer"),
        Some(&RouteTarget::Cell(cell_id(0x01)))
    );
    assert_eq!(governed.classify_path(b"/cells/oracle/price"), None);

    // --- Governance proposal: add oracle route ---
    let new_table = compile_routes(&[
        ("/cells/stablecoin/*", RouteTarget::Cell(cell_id(0x01))),
        ("/cells/oracle/*", RouteTarget::Cell(cell_id(0x02))),
        ("/intents/*", RouteTarget::Handler("intent_pool".into())),
    ]);

    // Simulate governance vote reaching threshold.
    // The proof carries the expected old commitment (CAS).
    let governance_proof = GovernanceProof {
        expected_old_commitment: initial_commitment,
        proof_data: vec![0xDE, 0xAD], // placeholder threshold signature
    };

    // Apply the update.
    let result = governed.update_routes(new_table, &governance_proof);
    assert!(result.is_ok(), "Governance update should succeed");

    // Commitment changed.
    assert_ne!(governed.commitment(), &initial_commitment);

    // New route is now active.
    assert_eq!(
        governed.classify_path(b"/cells/oracle/price"),
        Some(&RouteTarget::Cell(cell_id(0x02)))
    );
    // Old route still works.
    assert_eq!(
        governed.classify_path(b"/cells/stablecoin/transfer"),
        Some(&RouteTarget::Cell(cell_id(0x01)))
    );
}

// =============================================================================
// Test 4: Verify old classification changes after route amendment
// =============================================================================

/// After a route amendment, messages that previously went to one target now
/// go to a different target (or become unrouted).
#[test]
fn test_classification_changes_after_amendment() {
    let _harness = quick_federation();

    // Initial: stablecoin routes to cell_1.
    let table_v1 = compile_routes(&[("/cells/stablecoin/*", RouteTarget::Cell(cell_id(0x01)))]);
    let commitment_v1 = table_v1.commitment;
    let mut governed = GovernedRouter::new(table_v1);

    // Before amendment: stablecoin -> cell_1.
    assert_eq!(
        governed.classify_path(b"/cells/stablecoin/transfer"),
        Some(&RouteTarget::Cell(cell_id(0x01)))
    );

    // Amendment: stablecoin now routes to cell_2 (migration).
    let table_v2 = compile_routes(&[("/cells/stablecoin/*", RouteTarget::Cell(cell_id(0x02)))]);
    let proof = GovernanceProof {
        expected_old_commitment: commitment_v1,
        proof_data: vec![],
    };
    governed.update_routes(table_v2, &proof).unwrap();

    // After amendment: stablecoin -> cell_2 (changed!).
    assert_eq!(
        governed.classify_path(b"/cells/stablecoin/transfer"),
        Some(&RouteTarget::Cell(cell_id(0x02)))
    );
}

// =============================================================================
// Test 5: Revocation - remove a route -> messages get Drop classification
// =============================================================================

/// When a route is removed and replaced with Drop, messages to that path are
/// silently discarded rather than routed to a handler.
#[test]
fn test_route_revocation_classifies_as_drop() {
    let _harness = quick_federation();

    // Initial: oracle and stablecoin both route normally.
    let table_v1 = compile_routes(&[
        ("/cells/stablecoin/*", RouteTarget::Cell(cell_id(0x01))),
        ("/cells/oracle/*", RouteTarget::Cell(cell_id(0x02))),
    ]);
    let commitment_v1 = table_v1.commitment;
    let mut governed = GovernedRouter::new(table_v1);

    // Oracle is routable.
    assert_eq!(
        governed.classify_path(b"/cells/oracle/price"),
        Some(&RouteTarget::Cell(cell_id(0x02)))
    );

    // Revoke the oracle route: replace with Drop.
    let table_v2 = compile_routes(&[
        ("/cells/stablecoin/*", RouteTarget::Cell(cell_id(0x01))),
        ("/cells/oracle/*", RouteTarget::Drop),
    ]);
    let proof = GovernanceProof {
        expected_old_commitment: commitment_v1,
        proof_data: vec![],
    };
    governed.update_routes(table_v2, &proof).unwrap();

    // Oracle messages now get Drop classification.
    assert_eq!(
        governed.classify_path(b"/cells/oracle/price"),
        Some(&RouteTarget::Drop)
    );

    // Stablecoin still works.
    assert_eq!(
        governed.classify_path(b"/cells/stablecoin/transfer"),
        Some(&RouteTarget::Cell(cell_id(0x01)))
    );

    // Dispatch confirms discard behavior.
    let router = governed.router();
    assert_eq!(
        dispatch_path(router, b"/cells/oracle/anything"),
        DispatchDecision::Discard
    );
}

// =============================================================================
// Test 6: CAS semantics - wrong commitment rejects update
// =============================================================================

/// Route updates fail if the governance proof carries a stale commitment.
/// This prevents race conditions between concurrent governance proposals.
#[test]
fn test_cas_rejects_stale_commitment() {
    let _harness = quick_federation();

    let table_v1 = compile_routes(&[("/cells/alpha/*", RouteTarget::Cell(cell_id(0x01)))]);
    let mut governed = GovernedRouter::new(table_v1);

    // Attempt update with wrong commitment.
    let new_table = compile_routes(&[("/cells/alpha/*", RouteTarget::Cell(cell_id(0x02)))]);
    let bad_proof = GovernanceProof {
        expected_old_commitment: [0xFF; 32], // wrong
        proof_data: vec![],
    };

    let result = governed.update_routes(new_table, &bad_proof);
    assert!(matches!(
        result,
        Err(RouteUpdateError::CommitmentMismatch { .. })
    ));

    // Route unchanged.
    assert_eq!(
        governed.classify_path(b"/cells/alpha/x"),
        Some(&RouteTarget::Cell(cell_id(0x01)))
    );
}

// =============================================================================
// Test 7: Shared prefix routes disambiguate correctly
// =============================================================================

/// Routes with shared prefixes (e.g. /cells/alpha and /cells/alpha-beta)
/// are disambiguated by the DFA without interference.
#[test]
fn test_shared_prefix_disambiguation() {
    let _harness = quick_federation();

    let table = compile_routes(&[
        ("/cells/alpha/*", RouteTarget::Cell(cell_id(0x01))),
        ("/cells/alpha-beta/*", RouteTarget::Cell(cell_id(0x02))),
        ("/cells/alpha-gamma/*", RouteTarget::Cell(cell_id(0x03))),
    ]);
    let router = Router::new(table);

    assert_eq!(
        router.classify_path(b"/cells/alpha/action"),
        Some(&RouteTarget::Cell(cell_id(0x01)))
    );
    assert_eq!(
        router.classify_path(b"/cells/alpha-beta/action"),
        Some(&RouteTarget::Cell(cell_id(0x02)))
    );
    assert_eq!(
        router.classify_path(b"/cells/alpha-gamma/action"),
        Some(&RouteTarget::Cell(cell_id(0x03)))
    );
}

// =============================================================================
// Test 8: Raw wire message classification (binary prefix)
// =============================================================================

/// Simulate classifying a raw wire message that has a path-like prefix followed
/// by binary payload data. The DFA wildcard absorbs the entire message.
#[test]
fn test_raw_wire_message_classification() {
    let _harness = quick_federation();

    let table = compile_routes(&[("/cells/stablecoin/*", RouteTarget::Cell(cell_id(0x10)))]);
    let router = Router::new(table);

    // Wire message: path prefix + null separator + binary payload
    let msg = b"/cells/stablecoin/transfer\x00\x01\x02\x03\x04payload_bytes";
    assert_eq!(
        router.classify(msg),
        Some(&RouteTarget::Cell(cell_id(0x10)))
    );
}

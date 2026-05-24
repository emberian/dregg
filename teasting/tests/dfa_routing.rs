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
    cell_target, compile_routes, dispatch_path, federation_target, target_as_cell,
    target_as_federation,
};

fn cell_id(byte: u8) -> CellId {
    CellId([byte; 32])
}

fn fed_id(byte: u8) -> FederationId {
    FederationId([byte; 32])
}

fn good_proof(old: [u8; 32]) -> GovernanceProof {
    GovernanceProof {
        expected_old_commitment: old,
        // Stub verifier accepts any non-empty proof_data. In production
        // this is the threshold signature payload.
        proof_data: vec![0xAA, 0xBB],
    }
}

#[test]
fn test_compile_route_table() {
    let _harness = quick_federation();

    let table = compile_routes(&[
        ("/cells/stablecoin/*", cell_target(cell_id(0x01))),
        ("/cells/oracle/*", cell_target(cell_id(0x02))),
        ("/intents/*", RouteTarget::handler("intent_pool")),
        ("/admin/*", RouteTarget::handler("admin")),
        ("/federated/*", federation_target(fed_id(0x42))),
    ]);
    assert!(table.num_states > 5);
    assert_eq!(table.accept_map.len(), 5);
    assert_ne!(table.commitment, [0u8; 32]);

    let table2 = compile_routes(&[
        ("/cells/stablecoin/*", cell_target(cell_id(0x01))),
        ("/cells/oracle/*", cell_target(cell_id(0x02))),
        ("/intents/*", RouteTarget::handler("intent_pool")),
        ("/admin/*", RouteTarget::handler("admin")),
        ("/federated/*", federation_target(fed_id(0x42))),
    ]);
    assert_eq!(table.commitment, table2.commitment);
}

#[test]
fn test_classify_messages_to_correct_handlers() {
    let _harness = quick_federation();

    let table = compile_routes(&[
        ("/cells/stablecoin/*", cell_target(cell_id(0x01))),
        ("/cells/oracle/*", cell_target(cell_id(0x02))),
        ("/intents/*", RouteTarget::handler("intent_pool")),
        ("/admin/*", RouteTarget::handler("admin")),
        ("/federated/*", federation_target(fed_id(0x42))),
    ]);
    let router = Router::new(table);

    assert_eq!(
        target_as_cell(
            router
                .classify_path(b"/cells/stablecoin/transfer")
                .unwrap()
                .target
        ),
        Some(cell_id(0x01))
    );
    assert_eq!(
        target_as_cell(
            router
                .classify_path(b"/cells/stablecoin/balance")
                .unwrap()
                .target
        ),
        Some(cell_id(0x01))
    );
    assert_eq!(
        target_as_cell(
            router
                .classify_path(b"/cells/oracle/price_feed")
                .unwrap()
                .target
        ),
        Some(cell_id(0x02))
    );

    let c = router.classify_path(b"/intents/submit_swap").unwrap();
    assert_eq!(c.target, &RouteTarget::handler("intent_pool"));

    let c = router.classify_path(b"/admin/status").unwrap();
    assert_eq!(c.target, &RouteTarget::handler("admin"));

    assert_eq!(
        target_as_federation(router.classify_path(b"/federated/sync").unwrap().target),
        Some(fed_id(0x42))
    );

    assert!(router.classify_path(b"/unknown/path").is_none());
    assert!(router.classify_path(b"/cells/unknown/x").is_none());
}

#[test]
fn test_governance_route_update() {
    let _harness = quick_federation();

    let initial_table = compile_routes(&[
        ("/cells/stablecoin/*", cell_target(cell_id(0x01))),
        ("/intents/*", RouteTarget::handler("intent_pool")),
    ]);
    let initial_commitment = initial_table.commitment;
    let mut governed = GovernedRouter::new(initial_table);

    assert_eq!(
        target_as_cell(
            governed
                .classify_path(b"/cells/stablecoin/transfer")
                .unwrap()
                .target
        ),
        Some(cell_id(0x01))
    );
    assert!(governed.classify_path(b"/cells/oracle/price").is_none());

    let new_table = compile_routes(&[
        ("/cells/stablecoin/*", cell_target(cell_id(0x01))),
        ("/cells/oracle/*", cell_target(cell_id(0x02))),
        ("/intents/*", RouteTarget::handler("intent_pool")),
    ]);

    governed
        .update_routes(new_table, &good_proof(initial_commitment))
        .unwrap();

    assert_ne!(governed.commitment(), &initial_commitment);
    assert_eq!(
        target_as_cell(
            governed
                .classify_path(b"/cells/oracle/price")
                .unwrap()
                .target
        ),
        Some(cell_id(0x02))
    );
    assert_eq!(
        target_as_cell(
            governed
                .classify_path(b"/cells/stablecoin/transfer")
                .unwrap()
                .target
        ),
        Some(cell_id(0x01))
    );
}

#[test]
fn test_classification_changes_after_amendment() {
    let _harness = quick_federation();

    let table_v1 = compile_routes(&[("/cells/stablecoin/*", cell_target(cell_id(0x01)))]);
    let commitment_v1 = table_v1.commitment;
    let mut governed = GovernedRouter::new(table_v1);

    assert_eq!(
        target_as_cell(
            governed
                .classify_path(b"/cells/stablecoin/transfer")
                .unwrap()
                .target
        ),
        Some(cell_id(0x01))
    );

    let table_v2 = compile_routes(&[("/cells/stablecoin/*", cell_target(cell_id(0x02)))]);
    governed
        .update_routes(table_v2, &good_proof(commitment_v1))
        .unwrap();

    assert_eq!(
        target_as_cell(
            governed
                .classify_path(b"/cells/stablecoin/transfer")
                .unwrap()
                .target
        ),
        Some(cell_id(0x02))
    );
}

#[test]
fn test_route_revocation_classifies_as_drop() {
    let _harness = quick_federation();

    let table_v1 = compile_routes(&[
        ("/cells/stablecoin/*", cell_target(cell_id(0x01))),
        ("/cells/oracle/*", cell_target(cell_id(0x02))),
    ]);
    let commitment_v1 = table_v1.commitment;
    let mut governed = GovernedRouter::new(table_v1);

    assert_eq!(
        target_as_cell(
            governed
                .classify_path(b"/cells/oracle/price")
                .unwrap()
                .target
        ),
        Some(cell_id(0x02))
    );

    let table_v2 = compile_routes(&[
        ("/cells/stablecoin/*", cell_target(cell_id(0x01))),
        ("/cells/oracle/*", RouteTarget::Drop),
    ]);
    governed
        .update_routes(table_v2, &good_proof(commitment_v1))
        .unwrap();

    let c = governed.classify_path(b"/cells/oracle/price").unwrap();
    assert_eq!(c.target, &RouteTarget::Drop);

    assert_eq!(
        target_as_cell(
            governed
                .classify_path(b"/cells/stablecoin/transfer")
                .unwrap()
                .target
        ),
        Some(cell_id(0x01))
    );

    let router = governed.router();
    assert_eq!(
        dispatch_path(router, b"/cells/oracle/anything"),
        DispatchDecision::Discard
    );
}

#[test]
fn test_cas_rejects_stale_commitment() {
    let _harness = quick_federation();

    let table_v1 = compile_routes(&[("/cells/alpha/*", cell_target(cell_id(0x01)))]);
    let mut governed = GovernedRouter::new(table_v1);

    let new_table = compile_routes(&[("/cells/alpha/*", cell_target(cell_id(0x02)))]);
    let bad_proof = GovernanceProof {
        expected_old_commitment: [0xFF; 32],
        proof_data: vec![0xAA],
    };

    let result = governed.update_routes(new_table, &bad_proof);
    assert!(matches!(
        result,
        Err(RouteUpdateError::CommitmentMismatch { .. })
    ));

    assert_eq!(
        target_as_cell(governed.classify_path(b"/cells/alpha/x").unwrap().target),
        Some(cell_id(0x01))
    );
}

#[test]
fn test_shared_prefix_disambiguation() {
    let _harness = quick_federation();

    let table = compile_routes(&[
        ("/cells/alpha/*", cell_target(cell_id(0x01))),
        ("/cells/alpha-beta/*", cell_target(cell_id(0x02))),
        ("/cells/alpha-gamma/*", cell_target(cell_id(0x03))),
    ]);
    let router = Router::new(table);

    assert_eq!(
        target_as_cell(router.classify_path(b"/cells/alpha/action").unwrap().target),
        Some(cell_id(0x01))
    );
    assert_eq!(
        target_as_cell(
            router
                .classify_path(b"/cells/alpha-beta/action")
                .unwrap()
                .target
        ),
        Some(cell_id(0x02))
    );
    assert_eq!(
        target_as_cell(
            router
                .classify_path(b"/cells/alpha-gamma/action")
                .unwrap()
                .target
        ),
        Some(cell_id(0x03))
    );
}

#[test]
fn test_raw_wire_message_classification() {
    let _harness = quick_federation();

    let table = compile_routes(&[("/cells/stablecoin/*", cell_target(cell_id(0x10)))]);
    let router = Router::new(table);

    let msg = b"/cells/stablecoin/transfer\x00\x01\x02\x03\x04payload_bytes";
    let c = router.classify(msg).unwrap();
    assert_eq!(target_as_cell(c.target), Some(cell_id(0x10)));
}

//! DFA routing checks: compilation, classification, governance.

use pyana_captp::GroupId;
use pyana_types::CellId;
use pyana_wire::dfa_router::{
    GovernanceProof, GovernedRouter, RouteTarget, Router, compile_routes,
};

use crate::report::{CheckResult, run_check};

pub fn run() -> Vec<CheckResult> {
    vec![
        run_check("compile_routes", check_compile_routes),
        run_check("classify_messages", check_classify_messages),
        run_check("governance_update", check_governance_update),
        run_check("commitment_matches", check_commitment_matches),
    ]
}

fn make_test_routes() -> Vec<(&'static str, RouteTarget)> {
    let stablecoin_cell = CellId(*blake3::hash(b"stablecoin").as_bytes());
    let amm_cell = CellId(*blake3::hash(b"amm").as_bytes());
    let remote_fed = GroupId(*blake3::hash(b"remote-federation").as_bytes());

    vec![
        ("/cells/stablecoin/*", RouteTarget::Cell(stablecoin_cell)),
        ("/cells/amm/*", RouteTarget::Cell(amm_cell)),
        ("/intents/*", RouteTarget::Handler("intent_pool".into())),
        ("/admin", RouteTarget::Handler("admin".into())),
        ("/federation/remote/*", RouteTarget::Federation(remote_fed)),
        ("/blocked/*", RouteTarget::Drop),
    ]
}

fn check_compile_routes() -> Result<(), String> {
    let routes = make_test_routes();
    let table = compile_routes(&routes);

    // Verify the table was constructed with valid state count.
    if table.num_states < 2 {
        return Err(format!(
            "expected at least 2 states, got {}",
            table.num_states
        ));
    }

    // Verify commitment is non-zero.
    if table.commitment == [0u8; 32] {
        return Err("route table commitment should not be all zeros".into());
    }

    // Verify transitions table has the right size.
    let expected_size = table.num_states * 256;
    if table.transitions.len() != expected_size {
        return Err(format!(
            "transitions table size: expected {expected_size}, got {}",
            table.transitions.len()
        ));
    }

    Ok(())
}

fn check_classify_messages() -> Result<(), String> {
    let routes = make_test_routes();
    let table = compile_routes(&routes);
    let router = Router::new(table);

    // Test cell routing.
    let result = router.classify(b"/cells/stablecoin/transfer");
    match result {
        Some(RouteTarget::Cell(cell_id)) => {
            let expected = CellId(*blake3::hash(b"stablecoin").as_bytes());
            if *cell_id != expected {
                return Err("stablecoin route classified to wrong cell".into());
            }
        }
        other => return Err(format!("expected Cell target, got {:?}", other)),
    }

    // Test handler routing.
    let result = router.classify(b"/intents/broadcast");
    match result {
        Some(RouteTarget::Handler(name)) => {
            if name != "intent_pool" {
                return Err(format!("expected 'intent_pool' handler, got '{name}'"));
            }
        }
        other => return Err(format!("expected Handler target, got {:?}", other)),
    }

    // Test drop routing.
    let result = router.classify(b"/blocked/spam");
    match result {
        Some(RouteTarget::Drop) => {}
        other => return Err(format!("expected Drop target, got {:?}", other)),
    }

    // Test unmatched path goes to None (dead state).
    let result = router.classify(b"/unknown/path");
    if result.is_some() {
        return Err("unknown path should not match any route".into());
    }

    Ok(())
}

fn check_governance_update() -> Result<(), String> {
    let routes = make_test_routes();
    let table = compile_routes(&routes);
    let old_commitment = table.commitment;
    let mut governed = GovernedRouter::new(table);

    // Verify initial commitment.
    if *governed.commitment() != old_commitment {
        return Err("governed router commitment should match table commitment".into());
    }

    // Build a new route table (add a route).
    let new_cell = CellId(*blake3::hash(b"new-service").as_bytes());
    let mut new_routes = make_test_routes();
    new_routes.push(("/services/compute/*", RouteTarget::Cell(new_cell)));
    let new_table = compile_routes(&new_routes);
    let new_commitment = new_table.commitment;

    // Attempt update with correct old commitment (should succeed).
    let proof = GovernanceProof {
        expected_old_commitment: old_commitment,
        proof_data: vec![],
    };

    governed
        .update_routes(new_table, &proof)
        .map_err(|e| format!("governance update failed: {e}"))?;

    // Verify commitment changed.
    if *governed.commitment() != new_commitment {
        return Err("commitment should be updated after successful route update".into());
    }

    // Attempt update with stale commitment (should fail).
    let stale_proof = GovernanceProof {
        expected_old_commitment: old_commitment, // stale
        proof_data: vec![],
    };
    let stale_routes = compile_routes(&make_test_routes());
    let result = governed.update_routes(stale_routes, &stale_proof);
    if result.is_ok() {
        return Err("update with stale commitment should fail".into());
    }

    Ok(())
}

fn check_commitment_matches() -> Result<(), String> {
    let routes = make_test_routes();
    let table = compile_routes(&routes);
    let governed = GovernedRouter::new(table);

    // The commitment from the governed router should match what we'd compute
    // from the same route set.
    let table2 = compile_routes(&make_test_routes());
    if *governed.commitment() != table2.commitment {
        return Err("deterministic route compilation should produce same commitment".into());
    }

    // Verify classification still works through the governed router.
    let result = governed.classify(b"/cells/amm/swap");
    match result {
        Some(RouteTarget::Cell(cell_id)) => {
            let expected = CellId(*blake3::hash(b"amm").as_bytes());
            if *cell_id != expected {
                return Err("governed router amm route classified to wrong cell".into());
            }
        }
        other => return Err(format!("expected Cell target, got {:?}", other)),
    }

    Ok(())
}

//! DFA routing checks: compilation, classification, governance.

use pyana_captp::FederationId as GroupId;
use pyana_types::CellId;
use pyana_wire::dfa_router::{
    GovernanceProof, GovernedRouter, RouteTarget, Router, cell_target, compile_routes,
    federation_target, target_as_cell,
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
        ("/cells/stablecoin/*", cell_target(stablecoin_cell)),
        ("/cells/amm/*", cell_target(amm_cell)),
        ("/intents/*", RouteTarget::handler("intent_pool")),
        ("/admin", RouteTarget::handler("admin")),
        ("/federation/remote/*", federation_target(remote_fed)),
        ("/blocked/*", RouteTarget::Drop),
    ]
}

fn check_compile_routes() -> Result<(), String> {
    let routes = make_test_routes();
    let table = compile_routes(&routes);

    if table.num_states < 2 {
        return Err(format!(
            "expected at least 2 states, got {}",
            table.num_states
        ));
    }

    if table.commitment == [0u8; 32] {
        return Err("route table commitment should not be all zeros".into());
    }

    let expected_size = (table.num_states as usize) * 256;
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

    let stablecoin = CellId(*blake3::hash(b"stablecoin").as_bytes());
    let c = router
        .classify(b"/cells/stablecoin/transfer")
        .ok_or_else(|| "stablecoin route did not classify".to_string())?;
    match target_as_cell(c.target) {
        Some(id) if id == stablecoin => {}
        Some(id) => return Err(format!("stablecoin route classified to wrong cell: {id:?}")),
        None => return Err(format!("expected Cell target, got {:?}", c.target)),
    }

    let c = router
        .classify(b"/intents/broadcast")
        .ok_or_else(|| "intent route did not classify".to_string())?;
    match c.target {
        RouteTarget::Handler(name) if name == "intent_pool" => {}
        other => return Err(format!("expected Handler('intent_pool'), got {other:?}")),
    }

    let c = router
        .classify(b"/blocked/spam")
        .ok_or_else(|| "blocked route did not classify".to_string())?;
    if c.target != &RouteTarget::Drop {
        return Err(format!("expected Drop target, got {:?}", c.target));
    }

    if router.classify(b"/unknown/path").is_some() {
        return Err("unknown path should not match any route".into());
    }

    Ok(())
}

fn check_governance_update() -> Result<(), String> {
    let routes = make_test_routes();
    let table = compile_routes(&routes);
    let old_commitment = table.commitment;
    let mut governed = GovernedRouter::new(table);

    if *governed.commitment() != old_commitment {
        return Err("governed router commitment should match table commitment".into());
    }

    let new_cell = CellId(*blake3::hash(b"new-service").as_bytes());
    let mut new_routes = make_test_routes();
    new_routes.push(("/services/compute/*", cell_target(new_cell)));
    let new_table = compile_routes(&new_routes);
    let new_commitment = new_table.commitment;

    let proof = GovernanceProof {
        expected_old_commitment: old_commitment,
        // Stub verifier needs non-empty data; production wires real threshold sigs.
        proof_data: vec![0xAA, 0xBB],
    };

    governed
        .update_routes(new_table, &proof)
        .map_err(|e| format!("governance update failed: {e}"))?;

    if *governed.commitment() != new_commitment {
        return Err("commitment should be updated after successful route update".into());
    }

    let stale_proof = GovernanceProof {
        expected_old_commitment: old_commitment,
        proof_data: vec![0xAA, 0xBB],
    };
    let stale_routes = compile_routes(&make_test_routes());
    if governed.update_routes(stale_routes, &stale_proof).is_ok() {
        return Err("update with stale commitment should fail".into());
    }

    Ok(())
}

fn check_commitment_matches() -> Result<(), String> {
    let routes = make_test_routes();
    let table = compile_routes(&routes);
    let governed = GovernedRouter::new(table);

    let table2 = compile_routes(&make_test_routes());
    if *governed.commitment() != table2.commitment {
        return Err("deterministic route compilation should produce same commitment".into());
    }

    let amm = CellId(*blake3::hash(b"amm").as_bytes());
    let c = governed
        .classify(b"/cells/amm/swap")
        .ok_or_else(|| "amm route did not classify".to_string())?;
    match target_as_cell(c.target) {
        Some(id) if id == amm => {}
        Some(id) => return Err(format!("amm classified to wrong cell: {id:?}")),
        None => return Err(format!("expected Cell target, got {:?}", c.target)),
    }

    Ok(())
}

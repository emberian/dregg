//! 10-Agent Swarm Delegation Demo
//!
//! Demonstrates a realistic AI agent fleet pattern where a Controller spawns 10
//! worker agents via `SpawnWithDelegation`, each receiving a snapshot of the
//! controller's full capability set. Workers execute independently using their
//! delegated authority, refresh when capabilities change, and can be individually
//! revoked.
//!
//! The scenario:
//!
//! 1. Controller spawns 10 workers with snapshot+refresh delegation
//! 2. Workers execute 3 turns each (30 total) using delegated caps
//! 3. Controller gains new capability -> workers DON'T see it (snapshot frozen)
//! 4. Workers refresh -> pick up new capability
//! 5. Controller revokes one compromised worker (#7)
//! 6. Scaling analysis: delegation vs. individual grants
//! 7. Staleness semantics demonstration

use pyana_cell::{AuthRequired, Cell, CellId, DelegatedRef, Ledger, Permissions};
use pyana_turn::{
    Action, Authorization, CallForest, CommitmentMode, ComputronCosts, DelegationMode, Effect,
    TurnExecutor, TurnResult,
};
use pyana_turn::action::symbol;
use pyana_turn::turn::Turn;

const NUM_WORKERS: usize = 10;
const TURNS_PER_WORKER: usize = 3;

/// Create a cell with open permissions and a given balance.
fn make_open_cell(seed: u8, balance: u64) -> Cell {
    let mut key = [0u8; 32];
    key[0] = seed;
    let token_id = [0u8; 32];
    let mut cell = Cell::with_balance(key, token_id, balance);
    cell.permissions = Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    };
    cell
}

fn short_id(id: &CellId) -> String {
    let b = id.as_bytes();
    format!("{:02x}{:02x}{:02x}{:02x}", b[0], b[1], b[2], b[3])
}

fn make_turn(agent: CellId, nonce: u64, action: Action) -> Turn {
    let mut forest = CallForest::new();
    forest.add_root(action);
    Turn {
        agent,
        nonce,
        fee: 0,
        call_forest: forest,
        valid_until: None,
        memo: None,
        previous_receipt_hash: None,
        depends_on: vec![],
    }
}

/// Derive a deterministic worker identity from an index.
fn worker_identity(index: usize) -> ([u8; 32], [u8; 32], CellId) {
    let mut pk = [0u8; 32];
    pk[0] = 0xW0;
    pk[1] = index as u8;
    // Use a distinct derivation to avoid collisions
    let pk_hash = *blake3::hash(&pk).as_bytes();
    let token_id = [0u8; 32];
    let cell_id = CellId::derive_raw(&pk_hash, &token_id);
    (pk_hash, token_id, cell_id)
}

fn main() {
    println!("=== Pyana 10-Agent Swarm Delegation Demo ===");
    println!("    Snapshot+Refresh coordination for parallel AI agent workers");
    println!();

    // =========================================================================
    // SETUP: Controller + 5 service cells
    // =========================================================================

    let mut ledger = Ledger::new();
    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_timestamp(1000);

    // Create the controller agent.
    let mut controller = make_open_cell(1, 10_000_000);
    let controller_id = controller.id;

    // Create 5 service cells that the controller has access to.
    let mut service_ids = Vec::new();
    for i in 0..5 {
        let svc = make_open_cell(100 + i, 0);
        let svc_id = svc.id;
        service_ids.push(svc_id);
        controller.capabilities.grant(svc_id, AuthRequired::None);
        ledger.insert_cell(svc).unwrap();
    }

    ledger.insert_cell(controller).unwrap();

    println!("Setup:");
    println!("  Controller: {}", short_id(&controller_id));
    println!("  Services:   {} cells (indices 0..5)", service_ids.len());
    for (i, sid) in service_ids.iter().enumerate() {
        println!("    service[{}]: {}", i, short_id(sid));
    }
    println!();

    // =========================================================================
    // STEP 1: Controller spawns 10 workers with SpawnWithDelegation
    //         Each worker gets the controller's full cap set as a snapshot
    //         max_staleness = 60 seconds
    // =========================================================================

    println!("Step 1: Controller spawns {} workers with SpawnWithDelegation", NUM_WORKERS);
    println!("        max_staleness = 60s, each gets snapshot of {} capabilities", service_ids.len());
    println!();

    let mut worker_ids: Vec<CellId> = Vec::new();

    for i in 0..NUM_WORKERS {
        let (pk, token_id, expected_id) = worker_identity(i);

        let spawn = Action {
            target: controller_id,
            method: symbol(&format!("spawn_worker_{}", i)),
            args: vec![],
            authorization: Authorization::None,
            preconditions: Default::default(),
            effects: vec![Effect::SpawnWithDelegation {
                child_public_key: pk,
                child_token_id: token_id,
                max_staleness: 60,
            }],
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
        };

        let nonce = ledger.get(&controller_id).unwrap().state.nonce;
        let turn = make_turn(controller_id, nonce, spawn);
        let result = executor.execute(&turn, &mut ledger);
        assert!(result.is_committed(), "Spawn worker {} failed", i);

        // Verify the child was created with delegation.
        let child = ledger.get(&expected_id).unwrap();
        assert!(child.delegation.is_some());
        let delegation = child.delegation.as_ref().unwrap();
        assert_eq!(delegation.snapshot.len(), service_ids.len());
        assert_eq!(delegation.max_staleness, 60);

        // Give worker some balance for future turns.
        ledger.get_mut(&expected_id).unwrap().state.balance = 100_000;

        worker_ids.push(expected_id);
        println!("  Worker {:2}: {} (snapshot: {} caps)", i, short_id(&expected_id), delegation.snapshot.len());
    }
    println!();
    println!("  All {} workers spawned with {} SpawnWithDelegation effects total.", NUM_WORKERS, NUM_WORKERS);
    println!();

    // =========================================================================
    // STEP 2: Workers execute independently (10 workers x 3 turns = 30 turns)
    //         Each worker acts on different target cells using delegated caps
    // =========================================================================

    println!("Step 2: Workers execute independently ({} workers x {} turns = {} total)",
             NUM_WORKERS, TURNS_PER_WORKER, NUM_WORKERS * TURNS_PER_WORKER);
    println!("        Each uses delegated capabilities (no network calls to controller)");
    println!();

    let mut total_committed = 0u64;

    for turn_idx in 0..TURNS_PER_WORKER {
        for worker_idx in 0..NUM_WORKERS {
            let worker_id = worker_ids[worker_idx];
            // Each worker writes to a service cell determined by (worker_idx + turn_idx) mod 5.
            let target_svc = service_ids[(worker_idx + turn_idx) % service_ids.len()];

            let value = {
                let mut v = [0u8; 32];
                v[0] = worker_idx as u8;
                v[1] = turn_idx as u8;
                v[2] = 0xAA;
                v
            };

            let write_action = Action {
                target: target_svc,
                method: symbol(&format!("worker_{}_turn_{}", worker_idx, turn_idx)),
                args: vec![],
                authorization: Authorization::None,
                preconditions: Default::default(),
                effects: vec![Effect::SetField {
                    cell: target_svc,
                    index: turn_idx % 8,
                    value,
                }],
                may_delegate: DelegationMode::None,
                commitment_mode: CommitmentMode::Full,
                balance_change: None,
            };

            let nonce = ledger.get(&worker_id).unwrap().state.nonce;
            let turn = make_turn(worker_id, nonce, write_action);
            let result = executor.execute(&turn, &mut ledger);
            assert!(
                result.is_committed(),
                "Worker {} turn {} failed (nonce={}, target={})",
                worker_idx, turn_idx, nonce, short_id(&target_svc)
            );
            total_committed += 1;
        }
    }

    println!("  {} turns committed successfully.", total_committed);
    println!("  All workers acted using delegated authority (snapshot-based, no controller contact).");
    println!();

    // =========================================================================
    // STEP 3: Controller gains new capability (new service)
    //         Workers DON'T see it (snapshot is frozen at spawn time)
    // =========================================================================

    println!("Step 3: Controller gains new capability (Service #5)");
    println!("        Workers' snapshots are FROZEN -- they cannot access the new service");
    println!();

    let new_service = make_open_cell(200, 0);
    let new_svc_id = new_service.id;
    ledger.insert_cell(new_service).unwrap();
    ledger
        .get_mut(&controller_id)
        .unwrap()
        .capabilities
        .grant(new_svc_id, AuthRequired::None);

    println!("  New service: {} (controller now has {} caps)", short_id(&new_svc_id), service_ids.len() + 1);

    // Worker 0 tries to access new service -> FAILS.
    let worker_0_id = worker_ids[0];
    let worker_0_nonce = ledger.get(&worker_0_id).unwrap().state.nonce;
    let try_new_svc = Action {
        target: new_svc_id,
        method: symbol("access_new_service"),
        args: vec![],
        authorization: Authorization::None,
        preconditions: Default::default(),
        effects: vec![Effect::SetField {
            cell: new_svc_id,
            index: 0,
            value: [0xFF; 32],
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
    };

    let turn = make_turn(worker_0_id, worker_0_nonce, try_new_svc);
    let result = executor.execute(&turn, &mut ledger);
    assert!(!result.is_committed(), "Worker should NOT access new service before refresh");
    println!("  Worker 0 tries new service: REJECTED (not in snapshot)");
    println!();

    // =========================================================================
    // STEP 4: Workers refresh -> get updated snapshot
    //         Each worker does RefreshDelegation -> gets updated snapshot
    //         Refresh is O(1) per worker
    // =========================================================================

    println!("Step 4: All {} workers refresh delegation (O(1) per worker)", NUM_WORKERS);
    println!("        After refresh, all workers can access the new service");
    println!();

    executor.set_timestamp(2000);

    for (i, worker_id) in worker_ids.iter().enumerate() {
        let nonce = ledger.get(worker_id).unwrap().state.nonce;
        let refresh = Action {
            target: *worker_id,
            method: symbol("refresh_delegation"),
            args: vec![],
            authorization: Authorization::None,
            preconditions: Default::default(),
            effects: vec![Effect::RefreshDelegation],
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
        };

        let turn = make_turn(*worker_id, nonce, refresh);
        let result = executor.execute(&turn, &mut ledger);
        assert!(result.is_committed(), "Worker {} refresh failed", i);
    }

    // Verify all workers now have 6 capabilities (5 original + 1 new).
    for (i, worker_id) in worker_ids.iter().enumerate() {
        let child = ledger.get(worker_id).unwrap();
        let delegation = child.delegation.as_ref().unwrap();
        assert_eq!(
            delegation.snapshot.len(),
            service_ids.len() + 1,
            "Worker {} should have {} caps after refresh",
            i,
            service_ids.len() + 1
        );
        assert!(delegation.has_capability(&new_svc_id));
    }

    println!("  All workers refreshed. Snapshot now has {} capabilities each.", service_ids.len() + 1);

    // Worker 0 can now access the new service.
    let worker_0_nonce = ledger.get(&worker_0_id).unwrap().state.nonce;
    let use_new_svc = Action {
        target: new_svc_id,
        method: symbol("access_new_service_after_refresh"),
        args: vec![],
        authorization: Authorization::None,
        preconditions: Default::default(),
        effects: vec![Effect::SetField {
            cell: new_svc_id,
            index: 0,
            value: [0xCC; 32],
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
    };

    let turn = make_turn(worker_0_id, worker_0_nonce, use_new_svc);
    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed(), "Worker 0 should access new service after refresh");
    println!("  Worker 0 accesses new service after refresh: SUCCESS");
    println!();

    // =========================================================================
    // STEP 5: Controller revokes one compromised worker (#7)
    //         RevokeDelegation clears worker 7's snapshot immediately
    //         Other 9 workers are unaffected
    // =========================================================================

    println!("Step 5: Controller revokes compromised Worker #7");
    println!("        Single RevokeDelegation effect clears worker 7's entire snapshot");
    println!();

    let compromised_worker = worker_ids[7];

    // Controller needs capability to the child for RevokeDelegation.
    ledger
        .get_mut(&controller_id)
        .unwrap()
        .capabilities
        .grant(compromised_worker, AuthRequired::None);

    let controller_nonce = ledger.get(&controller_id).unwrap().state.nonce;
    let revoke = Action {
        target: controller_id,
        method: symbol("revoke_compromised_worker"),
        args: vec![],
        authorization: Authorization::None,
        preconditions: Default::default(),
        effects: vec![Effect::RevokeDelegation {
            child: compromised_worker,
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
    };

    let turn = make_turn(controller_id, controller_nonce, revoke);
    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed(), "Revocation should succeed");

    // Verify worker 7's delegation is cleared.
    let revoked = ledger.get(&compromised_worker).unwrap();
    assert!(revoked.delegation.is_none(), "Worker 7 delegation should be None after revocation");
    println!("  Worker 7 delegation: CLEARED (None)");

    // Verify other 9 workers are unaffected.
    for (i, worker_id) in worker_ids.iter().enumerate() {
        if i == 7 {
            continue;
        }
        let w = ledger.get(worker_id).unwrap();
        assert!(
            w.delegation.is_some(),
            "Worker {} should still have delegation",
            i
        );
        assert_eq!(w.delegation.as_ref().unwrap().snapshot.len(), service_ids.len() + 1);
    }
    println!("  Other 9 workers: UNAFFECTED (still have {} caps each)", service_ids.len() + 1);

    // Worker 7 tries to act -> FAILS.
    let w7_nonce = ledger.get(&compromised_worker).unwrap().state.nonce;
    let w7_try = Action {
        target: service_ids[0],
        method: symbol("worker_7_post_revocation"),
        args: vec![],
        authorization: Authorization::None,
        preconditions: Default::default(),
        effects: vec![Effect::SetField {
            cell: service_ids[0],
            index: 0,
            value: [0xDE; 32],
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
    };

    let turn = make_turn(compromised_worker, w7_nonce, w7_try);
    let result = executor.execute(&turn, &mut ledger);
    assert!(!result.is_committed(), "Revoked worker 7 should not be able to act");
    println!("  Worker 7 tries to act: REJECTED (delegation revoked)");

    // Worker 3 (unaffected) can still act.
    let w3_id = worker_ids[3];
    let w3_nonce = ledger.get(&w3_id).unwrap().state.nonce;
    let w3_action = Action {
        target: service_ids[2],
        method: symbol("worker_3_still_works"),
        args: vec![],
        authorization: Authorization::None,
        preconditions: Default::default(),
        effects: vec![Effect::SetField {
            cell: service_ids[2],
            index: 7,
            value: [0xBE; 32],
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
    };

    let turn = make_turn(w3_id, w3_nonce, w3_action);
    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed(), "Worker 3 should still function");
    println!("  Worker 3 still acts normally: SUCCESS");
    println!();

    // =========================================================================
    // STEP 6: Scaling analysis
    // =========================================================================

    println!("Step 6: Scaling Analysis");
    println!();
    println!("  WITHOUT delegation (individual GrantCapability):");
    println!("    Initial setup: {} workers x {} caps = {} GrantCapability effects",
             NUM_WORKERS, service_ids.len(), NUM_WORKERS * service_ids.len());
    println!("    New capability: {} additional GrantCapability effects (one per worker)",
             NUM_WORKERS);
    println!("    Revocation: revoke {} caps from compromised worker = {} RevokeCapability effects",
             service_ids.len() + 1, service_ids.len() + 1);
    println!("    Total for lifecycle: {} effects",
             NUM_WORKERS * service_ids.len() + NUM_WORKERS + service_ids.len() + 1);
    println!();
    println!("  WITH delegation (snapshot+refresh):");
    println!("    Initial setup: {} SpawnWithDelegation effects (one snapshot each)",
             NUM_WORKERS);
    println!("    New capability: {} RefreshDelegation effects (workers pull when ready)",
             NUM_WORKERS);
    println!("    Revocation: 1 RevokeDelegation effect (clears entire snapshot at once)");
    println!("    Total for lifecycle: {} effects", NUM_WORKERS + NUM_WORKERS + 1);
    println!();

    let without = NUM_WORKERS * service_ids.len() + NUM_WORKERS + service_ids.len() + 1;
    let with = NUM_WORKERS + NUM_WORKERS + 1;
    println!("  Reduction: {} effects -> {} effects ({:.1}x fewer)",
             without, with, without as f64 / with as f64);
    println!("  Key insight: delegation cost is O(workers), not O(workers x caps).");
    println!();

    // =========================================================================
    // STEP 7: Staleness semantics
    // =========================================================================

    println!("Step 7: Staleness Semantics");
    println!("        max_staleness = 60s; executor does NOT enforce it -- acceptors do");
    println!();

    // Create a delegation reference for demonstration.
    let demo_delegation = DelegatedRef::new(
        controller_id,
        vec![], // snapshot content doesn't matter for staleness check
        0,
        2000,   // refreshed_at = 2000 (from step 4)
        60,     // max_staleness = 60s
    );

    // Simulate various timestamps.
    let test_cases: &[(u64, &str)] = &[
        (2010, "10s after refresh -- within window"),
        (2030, "30s after refresh -- within window"),
        (2059, "59s after refresh -- just within window"),
        (2060, "60s after refresh -- at boundary (NOT stale: <=)"),
        (2061, "61s after refresh -- past boundary (STALE)"),
        (2120, "120s after refresh -- way past (STALE)"),
    ];

    for (now, description) in test_cases {
        let stale = demo_delegation.is_stale(*now);
        let status = if stale { "STALE" } else { "FRESH" };
        println!("  t={}: {} [{}]", now, description, status);
    }
    println!();
    println!("  A strict verifier rejects STALE delegations.");
    println!("  Workers should call RefreshDelegation before max_staleness expires.");
    println!("  This enables offline operation: workers act without contacting the controller.");
    println!();

    // Demonstrate the refresh-clears-staleness pattern.
    println!("  After refresh at t=2000, worker is fresh.");
    println!("  Time passes to t=2100 (stale). Worker refreshes again:");

    executor.set_timestamp(2100);
    let w0_nonce = ledger.get(&worker_0_id).unwrap().state.nonce;
    let refresh_again = Action {
        target: worker_0_id,
        method: symbol("refresh_after_stale"),
        args: vec![],
        authorization: Authorization::None,
        preconditions: Default::default(),
        effects: vec![Effect::RefreshDelegation],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
    };

    let turn = make_turn(worker_0_id, w0_nonce, refresh_again);
    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());

    let w0 = ledger.get(&worker_0_id).unwrap();
    let d = w0.delegation.as_ref().unwrap();
    assert_eq!(d.refreshed_at, 2100);
    assert!(!d.is_stale(2100));
    assert!(!d.is_stale(2160)); // within 60s window
    assert!(d.is_stale(2161));  // just past window
    println!("  Worker 0 refreshed at t=2100: is_stale(2160)={}, is_stale(2161)={}",
             d.is_stale(2160), d.is_stale(2161));
    println!();

    // =========================================================================
    // SUMMARY
    // =========================================================================

    println!("=== Demo Complete ===");
    println!();
    println!("Key properties demonstrated:");
    println!("  [1] Snapshot delegation: {} workers spawned with O(1) effect each", NUM_WORKERS);
    println!("  [2] Parallel execution: {} turns committed using delegated authority", total_committed);
    println!("  [3] Frozen snapshots: new caps invisible until explicit refresh");
    println!("  [4] Batch refresh: all workers update with O(1) RefreshDelegation each");
    println!("  [5] Targeted revocation: 1 RevokeDelegation clears 1 worker, 9 unaffected");
    println!("  [6] Scaling: O(workers) not O(workers x caps) for lifecycle management");
    println!("  [7] Eventual consistency: staleness bounded by max_staleness, acceptor-checked");
    println!();
    println!("Real-world analog: AI agent fleet where:");
    println!("  - Controller = orchestrator with platform-level access");
    println!("  - Workers = task-specific agents operating independently");
    println!("  - Delegation = workers inherit authority without per-request approval");
    println!("  - Refresh = workers sync capabilities at their own pace");
    println!("  - Revocation = instant isolation of compromised agents");
}

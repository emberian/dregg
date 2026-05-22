//! Snapshot+Refresh Delegation Demo
//!
//! Demonstrates the E-style delegation model where a child cell inherits its
//! parent's capabilities as a point-in-time SNAPSHOT. The lifecycle:
//!
//! 1. Parent spawns child with delegation (3 capabilities)
//! 2. Child acts using delegated capabilities
//! 3. Parent gains a new capability -> child cannot use it yet
//! 4. Child refreshes -> now has the new capability
//! 5. Parent revokes delegation -> child's snapshot is cleared
//!
//! This models real-world patterns: a supervisor delegates authority to workers,
//! workers operate offline using the snapshot, and revocation is eventual
//! (bounded by max_staleness).

use pyana_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
use pyana_turn::action::symbol;
use pyana_turn::turn::Turn;
use pyana_turn::{
    Action, Authorization, CallForest, CallTree, CommitmentMode, ComputronCosts, DelegationMode,
    Effect, TurnExecutor, TurnResult,
};

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

fn main() {
    println!("=== Pyana Snapshot+Refresh Delegation Demo ===");
    println!("    E-style capability inheritance with eventual revocation");
    println!();

    // =========================================================================
    // SETUP
    // =========================================================================

    let mut ledger = Ledger::new();
    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_timestamp(1000);

    // Create parent and 3 service cells.
    let mut parent = make_open_cell(1, 1_000_000);
    let parent_id = parent.id;

    let service_a = make_open_cell(10, 0);
    let service_b = make_open_cell(11, 0);
    let service_c = make_open_cell(12, 0);
    let svc_a_id = service_a.id;
    let svc_b_id = service_b.id;
    let svc_c_id = service_c.id;

    // Parent holds capabilities to all 3 services.
    parent.capabilities.grant(svc_a_id, AuthRequired::None);
    parent.capabilities.grant(svc_b_id, AuthRequired::None);
    parent.capabilities.grant(svc_c_id, AuthRequired::None);

    ledger.insert_cell(parent).unwrap();
    ledger.insert_cell(service_a).unwrap();
    ledger.insert_cell(service_b).unwrap();
    ledger.insert_cell(service_c).unwrap();

    println!("Setup:");
    println!("  Parent:    {}", short_id(&parent_id));
    println!("  Service A: {}", short_id(&svc_a_id));
    println!("  Service B: {}", short_id(&svc_b_id));
    println!("  Service C: {}", short_id(&svc_c_id));
    println!();

    // =========================================================================
    // STEP 1: Parent spawns child with delegation (3 caps, 300s staleness)
    // =========================================================================

    let child_pk = [42u8; 32];
    let child_token = [0u8; 32];
    let child_id = CellId::derive_raw(&child_pk, &child_token);

    println!("Step 1: Parent spawns child with delegation (max_staleness=300s)");

    let spawn = Action {
        target: parent_id,
        method: symbol("spawn_delegated_worker"),
        args: vec![],
        authorization: Authorization::None,
        preconditions: Default::default(),
        effects: vec![Effect::SpawnWithDelegation {
            child_public_key: child_pk,
            child_token_id: child_token,
            max_staleness: 300,
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
    };

    let turn = make_turn(parent_id, 0, spawn);
    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());

    let child = ledger.get(&child_id).unwrap();
    let delegation = child.delegation.as_ref().unwrap();
    println!("  Child {} created", short_id(&child_id));
    println!(
        "  Delegation snapshot: {} capabilities",
        delegation.snapshot.len()
    );
    println!(
        "  - has Service A: {}",
        delegation.has_capability(&svc_a_id)
    );
    println!(
        "  - has Service B: {}",
        delegation.has_capability(&svc_b_id)
    );
    println!(
        "  - has Service C: {}",
        delegation.has_capability(&svc_c_id)
    );
    println!("  Refreshed at: {}", delegation.refreshed_at);
    println!("  Delegation epoch: {}", delegation.delegation_epoch);
    println!();

    // =========================================================================
    // STEP 2: Child acts on Service A using delegated capability
    // =========================================================================

    println!("Step 2: Child uses delegated cap to write to Service A");

    // Give child some balance.
    ledger.get_mut(&child_id).unwrap().state.balance = 100_000;

    let value = [0xAA; 32];
    let child_write = Action {
        target: svc_a_id,
        method: symbol("write_config"),
        args: vec![],
        authorization: Authorization::None,
        preconditions: Default::default(),
        effects: vec![Effect::SetField {
            cell: svc_a_id,
            index: 0,
            value,
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
    };

    let turn = make_turn(child_id, 0, child_write);
    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());
    println!("  SUCCESS: Child wrote to Service A field[0]");
    println!();

    // =========================================================================
    // STEP 3: Parent gains new cap -> child cannot use it
    // =========================================================================

    println!("Step 3: Parent gains capability to new Service D");

    let service_d = make_open_cell(13, 0);
    let svc_d_id = service_d.id;
    ledger.insert_cell(service_d).unwrap();
    ledger
        .get_mut(&parent_id)
        .unwrap()
        .capabilities
        .grant(svc_d_id, AuthRequired::None);

    println!("  Service D: {}", short_id(&svc_d_id));
    println!("  Parent now has 4 capabilities");

    // Child tries to use Service D.
    // Note: Even failed turns consume the nonce (Phase 1 is never rolled back).
    let child_nonce = ledger.get(&child_id).unwrap().state.nonce;
    let child_try_d = Action {
        target: svc_d_id,
        method: symbol("use_d"),
        args: vec![],
        authorization: Authorization::None,
        preconditions: Default::default(),
        effects: vec![],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
    };

    let turn = make_turn(child_id, child_nonce, child_try_d);
    let result = executor.execute(&turn, &mut ledger);
    assert!(!result.is_committed());
    println!("  EXPECTED FAILURE: Child cannot use Service D (not in snapshot)");
    println!();

    // =========================================================================
    // STEP 4: Child refreshes -> picks up Service D
    // =========================================================================

    println!("Step 4: Child refreshes delegation (picks up Service D)");
    executor.set_timestamp(2000);

    let child_nonce = ledger.get(&child_id).unwrap().state.nonce;
    let refresh = Action {
        target: child_id,
        method: symbol("refresh_delegation"),
        args: vec![],
        authorization: Authorization::None,
        preconditions: Default::default(),
        effects: vec![Effect::RefreshDelegation],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
    };

    let turn = make_turn(child_id, child_nonce, refresh);
    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());

    let child = ledger.get(&child_id).unwrap();
    let delegation = child.delegation.as_ref().unwrap();
    println!(
        "  Snapshot updated: {} capabilities",
        delegation.snapshot.len()
    );
    println!(
        "  - has Service D: {}",
        delegation.has_capability(&svc_d_id)
    );
    println!("  Refreshed at: {}", delegation.refreshed_at);

    // Now child can use Service D.
    let child_nonce = ledger.get(&child_id).unwrap().state.nonce;
    let child_use_d = Action {
        target: svc_d_id,
        method: symbol("use_d"),
        args: vec![],
        authorization: Authorization::None,
        preconditions: Default::default(),
        effects: vec![Effect::SetField {
            cell: svc_d_id,
            index: 0,
            value: [0xDD; 32],
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
    };

    let turn = make_turn(child_id, child_nonce, child_use_d);
    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());
    println!("  SUCCESS: Child can now use Service D after refresh");
    println!();

    // =========================================================================
    // STEP 5: Parent revokes delegation
    // =========================================================================

    println!("Step 5: Parent revokes child's delegation");

    // Parent needs cap to child for RevokeDelegation.
    ledger
        .get_mut(&parent_id)
        .unwrap()
        .capabilities
        .grant(child_id, AuthRequired::None);

    let parent_nonce = ledger.get(&parent_id).unwrap().state.nonce;
    let revoke = Action {
        target: parent_id,
        method: symbol("revoke_worker"),
        args: vec![],
        authorization: Authorization::None,
        preconditions: Default::default(),
        effects: vec![Effect::RevokeDelegation { child: child_id }],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
    };

    let turn = make_turn(parent_id, parent_nonce, revoke);
    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed());

    let parent = ledger.get(&parent_id).unwrap();
    let child = ledger.get(&child_id).unwrap();
    println!(
        "  Parent delegation_epoch: {}",
        parent.state.delegation_epoch
    );
    println!(
        "  Child delegation: {:?}",
        child.delegation.as_ref().map(|_| "Some(...)")
    );
    println!("  Child delegation cleared: {}", child.delegation.is_none());

    // Child tries to use Service A again — now fails (delegation cleared).
    let child_nonce = ledger.get(&child_id).unwrap().state.nonce;
    let child_try_a = Action {
        target: svc_a_id,
        method: symbol("write_again"),
        args: vec![],
        authorization: Authorization::None,
        preconditions: Default::default(),
        effects: vec![Effect::SetField {
            cell: svc_a_id,
            index: 1,
            value: [0xBB; 32],
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
    };

    let turn = make_turn(child_id, child_nonce, child_try_a);
    let result = executor.execute(&turn, &mut ledger);
    assert!(!result.is_committed());
    println!("  EXPECTED FAILURE: Child cannot act after revocation");
    println!();

    // =========================================================================
    // STALENESS CHECK (library-level, not executor-enforced)
    // =========================================================================

    println!("Bonus: Staleness checking (acceptor-side)");

    let delegation = pyana_cell::DelegatedRef::new(
        parent_id,
        pyana_cell::CellId::from_bytes([0u8; 32]), // placeholder child
        vec![],
        0,
        1000,      // refreshed at t=1000
        300,       // max staleness 300s
        [0u8; 32], // clist_commitment
        [0u8; 64], // parent_signature
    );

    println!("  Delegation refreshed_at=1000, max_staleness=300");
    println!(
        "  is_stale(t=1100): {} (within window)",
        delegation.is_stale(1100)
    );
    println!(
        "  is_stale(t=1300): {} (at boundary)",
        delegation.is_stale(1300)
    );
    println!(
        "  is_stale(t=1301): {} (past boundary)",
        delegation.is_stale(1301)
    );
    println!(
        "  is_stale(t=2000): {} (way past)",
        delegation.is_stale(2000)
    );
    println!();

    println!("=== Demo Complete ===");
    println!("Key insight: revocation is EVENTUAL (bounded by max_staleness).");
    println!("The executor does NOT check staleness — that is the acceptor's job.");
    println!("This enables offline operation: children can act without contacting the parent.");
}

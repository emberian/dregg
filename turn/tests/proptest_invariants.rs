//! Property-based tests for turn crate invariants.
//!
//! Property 1: Capability confinement -- no cell ever holds a capability it wasn't
//!   explicitly granted, and no cell's capabilities are WIDER than what was granted.
//!
//! Property 2: Balance conservation -- sum of all cell balances == initial total
//!   minus fees for successful turns. No cell has negative balance.
//!
//! Property 4: Receipt chain integrity -- monotonically increasing nonces, state hash
//!   continuity, and verify_receipt_chain passes on valid chains / fails on tampered ones.
//!
//! Property 5: Delegation snapshot correctness -- after SpawnWithDelegation + random ops
//!   + RefreshDelegation, the child's snapshot matches the parent's current c-list.

use proptest::prelude::*;

use pyana_cell::{
    AuthRequired, CapabilityRef, CapabilitySet, Cell, CellId, Ledger, Permissions,
    capability::is_attenuation,
};
use pyana_turn::{
    Action, Authorization, CallForest, CallTree, ComputronCosts, DelegationMode, Effect,
    TurnExecutor, TurnReceipt, TurnResult,
    turn::Turn,
    verify::verify_receipt_chain,
};

// ============================================================================
// Helpers for generating random ledgers and operations
// ============================================================================

/// Create a cell with a specific seed (deterministic public key).
fn make_cell(seed: u8, balance: u64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(7);
    let token_id = [0u8; 32]; // same token domain
    Cell::with_balance(pk, token_id, balance)
}

/// Create a ledger with N cells, each having the given starting balance.
fn setup_ledger(n: u8, balance_each: u64) -> (Ledger, Vec<CellId>) {
    let mut ledger = Ledger::new();
    let mut ids = Vec::new();
    for i in 0..n {
        let cell = make_cell(i, balance_each);
        let id = cell.id;
        ledger.insert_cell(cell).unwrap();
        ids.push(id);
    }
    (ledger, ids)
}

/// Operations that can be applied to a ledger to test capability confinement.
#[derive(Clone, Debug)]
enum CapOp {
    /// Grant a capability from cell[from_idx] to cell[to_idx] targeting cell[target_idx].
    Grant { from_idx: usize, to_idx: usize, target_idx: usize, perm: AuthRequired },
    /// Revoke slot N from cell[cell_idx].
    Revoke { cell_idx: usize, slot: u32 },
    /// Introduce: cell[intro_idx] introduces cell[target_idx] to cell[recipient_idx].
    Introduce { intro_idx: usize, recipient_idx: usize, target_idx: usize, perm: AuthRequired },
}

/// Strategy for a random AuthRequired value.
fn arb_auth_required() -> impl Strategy<Value = AuthRequired> {
    prop_oneof![
        Just(AuthRequired::None),
        Just(AuthRequired::Signature),
        Just(AuthRequired::Proof),
        Just(AuthRequired::Either),
        Just(AuthRequired::Impossible),
    ]
}

/// Strategy for a random capability operation.
fn arb_cap_op(n_cells: usize) -> impl Strategy<Value = CapOp> {
    let n = n_cells;
    prop_oneof![
        (0..n, 0..n, 0..n, arb_auth_required()).prop_map(|(f, t, tgt, p)| CapOp::Grant {
            from_idx: f,
            to_idx: t,
            target_idx: tgt,
            perm: p,
        }),
        (0..n, 0..10u32).prop_map(|(c, s)| CapOp::Revoke { cell_idx: c, slot: s }),
        (0..n, 0..n, 0..n, arb_auth_required()).prop_map(|(i, r, t, p)| CapOp::Introduce {
            intro_idx: i,
            recipient_idx: r,
            target_idx: t,
            perm: p,
        }),
    ]
}

/// Strategy for a sequence of capability operations.
fn arb_cap_ops(n_cells: usize, max_ops: usize) -> impl Strategy<Value = Vec<CapOp>> {
    proptest::collection::vec(arb_cap_op(n_cells), 1..=max_ops)
}

// ============================================================================
// Property 1: Capability Confinement
// ============================================================================

/// A record of every grant ever issued, used to verify confinement.
#[derive(Clone, Debug)]
struct GrantRecord {
    to: CellId,
    target: CellId,
    perm: AuthRequired,
}

/// Execute capability operations directly on the ledger (bypassing executor auth
/// for speed -- we test the INVARIANT, not the executor's auth checks).
fn execute_cap_ops(
    ledger: &mut Ledger,
    ids: &[CellId],
    ops: &[CapOp],
    grants: &mut Vec<GrantRecord>,
) {
    for op in ops {
        match op {
            CapOp::Grant { from_idx, to_idx, target_idx, perm } => {
                let from_id = ids[*from_idx];
                let to_id = ids[*to_idx];
                let target_id = ids[*target_idx];

                // Check: from must hold a capability to target with permissions
                // at least as wide as `perm` (attenuation rule).
                let from_cell = ledger.get(&from_id).unwrap();
                let held = from_cell.capabilities.lookup_by_target(&target_id);
                let can_grant = match held {
                    Some(cap) => is_attenuation(&cap.permissions, perm),
                    None => false,
                };

                if can_grant {
                    let to_cell = ledger.get_mut(&to_id).unwrap();
                    to_cell.capabilities.grant(target_id, perm.clone());
                    grants.push(GrantRecord {
                        to: to_id,
                        target: target_id,
                        perm: perm.clone(),
                    });
                }
                // If can't grant, op is a no-op (doesn't violate confinement).
            }
            CapOp::Revoke { cell_idx, slot } => {
                let cell_id = ids[*cell_idx];
                let cell = ledger.get_mut(&cell_id).unwrap();
                cell.capabilities.revoke(*slot);
            }
            CapOp::Introduce { intro_idx, recipient_idx, target_idx, perm } => {
                let intro_id = ids[*intro_idx];
                let recipient_id = ids[*recipient_idx];
                let target_id = ids[*target_idx];

                // Introducer must hold capabilities to both recipient AND target.
                let intro_cell = ledger.get(&intro_id).unwrap();
                let has_recipient = intro_cell.capabilities.has_access(&recipient_id);
                let held_target = intro_cell.capabilities.lookup_by_target(&target_id);

                let can_introduce = has_recipient && match held_target {
                    Some(cap) => is_attenuation(&cap.permissions, perm),
                    None => false,
                };

                if can_introduce {
                    let recipient_cell = ledger.get_mut(&recipient_id).unwrap();
                    recipient_cell.capabilities.grant(target_id, perm.clone());
                    grants.push(GrantRecord {
                        to: recipient_id,
                        target: target_id,
                        perm: perm.clone(),
                    });
                }
            }
        }
    }
}

/// Assert the confinement invariant: every capability held by every cell was
/// explicitly granted, and is no wider than what was granted.
fn assert_confinement_invariant(ledger: &Ledger, ids: &[CellId], grants: &[GrantRecord]) {
    for id in ids {
        let cell = ledger.get(id).unwrap();
        for cap in cell.capabilities.iter() {
            // This capability must have been granted to this cell.
            let was_granted = grants.iter().any(|g| {
                g.to == *id && g.target == cap.target
                    && is_attenuation(&g.perm, &cap.permissions)
            });
            assert!(
                was_granted,
                "Cell {:?} holds capability to {:?} with perm {:?}, but no matching grant found",
                id, cap.target, cap.permissions
            );
        }
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(150))]

    #[test]
    fn proptest_capability_confinement_holds(ops in arb_cap_ops(5, 50)) {
        let (mut ledger, ids) = setup_ledger(5, 1000);

        // Bootstrap: give each cell a self-capability and capabilities to its neighbors.
        let mut grants: Vec<GrantRecord> = Vec::new();
        for i in 0..ids.len() {
            // Self-capability (needed for granting to others).
            {
                let cell = ledger.get_mut(&ids[i]).unwrap();
                cell.capabilities.grant(ids[i], AuthRequired::None);
                grants.push(GrantRecord {
                    to: ids[i],
                    target: ids[i],
                    perm: AuthRequired::None,
                });
            }
            // Capability to next neighbor (circular).
            let neighbor = ids[(i + 1) % ids.len()];
            {
                let cell = ledger.get_mut(&ids[i]).unwrap();
                cell.capabilities.grant(neighbor, AuthRequired::None);
                grants.push(GrantRecord {
                    to: ids[i],
                    target: neighbor,
                    perm: AuthRequired::None,
                });
            }
        }

        execute_cap_ops(&mut ledger, &ids, &ops, &mut grants);
        assert_confinement_invariant(&ledger, &ids, &grants);
    }
}

// ============================================================================
// Property 2: Balance Conservation
// ============================================================================

/// Operations for balance testing via the executor.
#[derive(Clone, Debug)]
enum BalanceOp {
    /// Transfer amount from cell[from_idx] to cell[to_idx].
    Transfer { from_idx: usize, to_idx: usize, amount: u64 },
}

fn arb_balance_op(n_cells: usize) -> impl Strategy<Value = BalanceOp> {
    (0..n_cells, 0..n_cells, 1u64..500u64).prop_map(|(f, t, a)| BalanceOp::Transfer {
        from_idx: f,
        to_idx: t,
        amount: a,
    })
}

fn arb_balance_ops(n_cells: usize, max_ops: usize) -> impl Strategy<Value = Vec<BalanceOp>> {
    proptest::collection::vec(arb_balance_op(n_cells), 1..=max_ops)
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(150))]

    #[test]
    fn proptest_balance_conservation_holds(ops in arb_balance_ops(4, 30)) {
        let initial_balance = 10_000u64;
        let n_cells = 4u8;
        let (mut ledger, ids) = setup_ledger(n_cells, initial_balance);
        let initial_total = initial_balance * (n_cells as u64);

        // Give each cell capabilities to all others (for transfers) and set
        // permissions to allow sends without signature (for testing conservation).
        for i in 0..ids.len() {
            let cell = ledger.get_mut(&ids[i]).unwrap();
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
            for j in 0..ids.len() {
                if i != j {
                    cell.capabilities.grant(ids[j], AuthRequired::None);
                }
            }
        }

        let executor = TurnExecutor::new(ComputronCosts::zero());
        let mut total_fees = 0u64;

        for op in &ops {
            match op {
                BalanceOp::Transfer { from_idx, to_idx, amount } => {
                    let from_id = ids[*from_idx];
                    let to_id = ids[*to_idx];
                    if from_id == to_id {
                        continue; // self-transfer is a no-op
                    }

                    let nonce = ledger.get(&from_id).unwrap().state.nonce;
                    let fee = 0u64; // zero-cost for conservation testing

                    let mut forest = CallForest::new();
                    let action = Action {
                        target: from_id,
                        method: [0u8; 32],
                        args: vec![],
                        authorization: Authorization::None,
                        preconditions: Default::default(),
                        effects: vec![Effect::Transfer {
                            from: from_id,
                            to: to_id,
                            amount: *amount,
                        }],
                        may_delegate: DelegationMode::None,
                        commitment_mode: Default::default(),
                        balance_change: None,
                    };
                    forest.add_root(action);

                    let turn = Turn {
                        agent: from_id,
                        nonce,
                        call_forest: forest,
                        fee,
                        memo: None,
                        valid_until: None,
                        previous_receipt_hash: None,
                        depends_on: vec![],
                    };

                    let result = executor.execute(&turn, &mut ledger);
                    if result.is_committed() {
                        total_fees += fee;
                    }
                    // If rejected (e.g. insufficient balance), that's fine.
                }
            }
        }

        // INVARIANT: sum of all balances == initial_total - total_fees
        let current_total: u64 = ids.iter().map(|id| ledger.get(id).unwrap().state.balance).sum();
        prop_assert_eq!(current_total, initial_total - total_fees,
            "Balance conservation violated: initial={}, fees={}, current={}",
            initial_total, total_fees, current_total);

        // INVARIANT: no cell has "negative" balance (u64 can't be negative, but
        // we verify no underflow panic occurred by reaching this point).
        for id in &ids {
            let balance = ledger.get(id).unwrap().state.balance;
            // This is trivially true for u64, but documents the invariant.
            prop_assert!(balance <= initial_total,
                "Cell balance {} exceeds initial total {}", balance, initial_total);
        }
    }
}

// ============================================================================
// Property 4: Receipt Chain Integrity
// ============================================================================

/// Build a valid receipt chain of length N for a given agent in a ledger.
fn build_receipt_chain(
    executor: &TurnExecutor,
    ledger: &mut Ledger,
    agent: CellId,
    n: usize,
) -> Vec<TurnReceipt> {
    let mut chain = Vec::new();

    for i in 0..n {
        let nonce = ledger.get(&agent).unwrap().state.nonce;
        let fee = 0u64;

        // Simple no-op action (targets self, no effects that need auth).
        let mut forest = CallForest::new();
        let action = Action {
            target: agent,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::None,
            preconditions: Default::default(),
            effects: vec![],
            may_delegate: DelegationMode::None,
            commitment_mode: Default::default(),
            balance_change: None,
        };
        forest.add_root(action);

        let previous_receipt_hash = chain.last().map(|r: &TurnReceipt| r.receipt_hash());

        let turn = Turn {
            agent,
            nonce,
            call_forest: forest,
            fee,
            memo: None,
            valid_until: None,
            previous_receipt_hash,
            depends_on: vec![],
        };

        let result = executor.execute(&turn, ledger);
        match result {
            TurnResult::Committed { receipt, .. } => {
                chain.push(receipt);
            }
            other => {
                panic!("Expected committed turn at index {i}, got: {other:?}");
            }
        }
    }

    chain
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    #[test]
    fn proptest_receipt_chain_integrity(chain_len in 2usize..15) {
        let (mut ledger, ids) = setup_ledger(1, 100_000);
        let agent = ids[0];

        // Set permissions to allow no-auth actions.
        {
            let cell = ledger.get_mut(&agent).unwrap();
            cell.permissions.access = AuthRequired::None;
        }

        let executor = TurnExecutor::new(ComputronCosts::zero());
        let chain = build_receipt_chain(&executor, &mut ledger, agent, chain_len);

        // INVARIANT: verify_receipt_chain passes on the full chain.
        prop_assert!(verify_receipt_chain(&chain).is_ok(),
            "Valid chain should pass verification");

        // INVARIANT: Monotonically increasing nonces (implied by executor nonce check).
        // We verify via the state hash chain instead -- each receipt links to previous.

        // INVARIANT: Each receipt's pre_state_hash == previous receipt's post_state_hash.
        for i in 1..chain.len() {
            prop_assert_eq!(chain[i].pre_state_hash, chain[i - 1].post_state_hash,
                "State chain broken at index {}", i);
        }

        // INVARIANT: Removing any receipt from the middle breaks verification.
        if chain.len() >= 3 {
            for remove_idx in 1..chain.len() - 1 {
                let mut broken_chain = chain.clone();
                broken_chain.remove(remove_idx);
                prop_assert!(verify_receipt_chain(&broken_chain).is_err(),
                    "Removing receipt at index {} should break verification", remove_idx);
            }
        }
    }

    /// Swapping two adjacent receipts should also break the chain.
    #[test]
    fn proptest_receipt_chain_swap_breaks(chain_len in 3usize..10) {
        let (mut ledger, ids) = setup_ledger(1, 100_000);
        let agent = ids[0];
        {
            let cell = ledger.get_mut(&agent).unwrap();
            cell.permissions.access = AuthRequired::None;
        }

        let executor = TurnExecutor::new(ComputronCosts::zero());
        let chain = build_receipt_chain(&executor, &mut ledger, agent, chain_len);

        // Swap receipts at positions 1 and 2.
        let mut swapped = chain.clone();
        swapped.swap(1, 2);
        prop_assert!(verify_receipt_chain(&swapped).is_err(),
            "Swapping receipts should break verification");
    }
}

// ============================================================================
// Property 5: Delegation Snapshot Correctness
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    #[test]
    fn proptest_delegation_snapshot_correctness(
        extra_caps in 0u8..5,
        revoke_before_refresh in proptest::bool::ANY,
    ) {
        let (mut ledger, ids) = setup_ledger(3, 10_000);
        let parent_id = ids[0];
        let target_a = ids[1];
        let target_b = ids[2];

        // Set all permissions to None for easy testing.
        for id in &ids {
            let cell = ledger.get_mut(id).unwrap();
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
        }

        // Give parent capabilities.
        {
            let parent = ledger.get_mut(&parent_id).unwrap();
            parent.capabilities.grant(target_a, AuthRequired::Signature);
            parent.capabilities.grant(target_b, AuthRequired::None);
        }

        // Spawn a child with delegation from the parent.
        let child_pk = [42u8; 32];
        let child_token = [0u8; 32];
        let child_id = CellId::derive_raw(&child_pk, &child_token);

        let executor = TurnExecutor::new(ComputronCosts::zero());

        // SpawnWithDelegation turn.
        {
            let nonce = ledger.get(&parent_id).unwrap().state.nonce;
            let mut forest = CallForest::new();
            let action = Action {
                target: parent_id,
                method: [0u8; 32],
                args: vec![],
                authorization: Authorization::None,
                preconditions: Default::default(),
                effects: vec![Effect::SpawnWithDelegation {
                    child_public_key: child_pk,
                    child_token_id: child_token,
                    max_staleness: 3600,
                }],
                may_delegate: DelegationMode::None,
                commitment_mode: Default::default(),
                balance_change: None,
            };
            forest.add_root(action);

            let turn = Turn {
                agent: parent_id,
                nonce,
                call_forest: forest,
                fee: 0,
                memo: None,
                valid_until: None,
                previous_receipt_hash: None,
                depends_on: vec![],
            };

            let result = executor.execute(&turn, &mut ledger);
            prop_assert!(result.is_committed(), "SpawnWithDelegation should succeed");
        }

        // Verify initial delegation snapshot matches parent's c-list at spawn time.
        {
            let child = ledger.get(&child_id).unwrap();
            let delegation = child.delegation.as_ref().unwrap();
            // At spawn time parent had 2 capabilities (target_a, target_b).
            prop_assert_eq!(delegation.snapshot.len(), 2,
                "Initial snapshot should have 2 capabilities");
        }

        // Modify parent's capabilities (add more).
        for i in 0..extra_caps {
            let new_target_cell = make_cell(100 + i, 1000);
            let new_target_id = new_target_cell.id;
            ledger.insert_cell(new_target_cell).unwrap();
            // Set permissions to None on new cell.
            ledger.get_mut(&new_target_id).unwrap().permissions = Permissions {
                send: AuthRequired::None,
                receive: AuthRequired::None,
                set_state: AuthRequired::None,
                set_permissions: AuthRequired::None,
                set_verification_key: AuthRequired::None,
                increment_nonce: AuthRequired::None,
                delegate: AuthRequired::None,
                access: AuthRequired::None,
            };
            let parent = ledger.get_mut(&parent_id).unwrap();
            parent.capabilities.grant(new_target_id, AuthRequired::None);
        }

        if revoke_before_refresh {
            // Revoke the delegation from the parent's side.
            let nonce = ledger.get(&parent_id).unwrap().state.nonce;
            let mut forest = CallForest::new();
            let action = Action {
                target: parent_id,
                method: [0u8; 32],
                args: vec![],
                authorization: Authorization::None,
                preconditions: Default::default(),
                effects: vec![Effect::RevokeDelegation { child: child_id }],
                may_delegate: DelegationMode::None,
                commitment_mode: Default::default(),
                balance_change: None,
            };
            forest.add_root(action);

            let turn = Turn {
                agent: parent_id,
                nonce,
                call_forest: forest,
                fee: 0,
                memo: None,
                valid_until: None,
                previous_receipt_hash: None,
                depends_on: vec![],
            };

            let result = executor.execute(&turn, &mut ledger);
            prop_assert!(result.is_committed(), "RevokeDelegation should succeed");

            // INVARIANT: After RevokeDelegation, child's delegation is None.
            let child = ledger.get(&child_id).unwrap();
            prop_assert!(child.delegation.is_none(),
                "After revocation, child delegation should be None");
        } else {
            // RefreshDelegation: child picks up parent's current c-list.
            // Need to give child permission for access.
            {
                let child_cell = ledger.get_mut(&child_id).unwrap();
                child_cell.permissions = Permissions {
                    send: AuthRequired::None,
                    receive: AuthRequired::None,
                    set_state: AuthRequired::None,
                    set_permissions: AuthRequired::None,
                    set_verification_key: AuthRequired::None,
                    increment_nonce: AuthRequired::None,
                    delegate: AuthRequired::None,
                    access: AuthRequired::None,
                };
            }

            let nonce = ledger.get(&child_id).unwrap().state.nonce;
            let mut forest = CallForest::new();
            let action = Action {
                target: child_id,
                method: [0u8; 32],
                args: vec![],
                authorization: Authorization::None,
                preconditions: Default::default(),
                effects: vec![Effect::RefreshDelegation],
                may_delegate: DelegationMode::None,
                commitment_mode: Default::default(),
                balance_change: None,
            };
            forest.add_root(action);

            let turn = Turn {
                agent: child_id,
                nonce,
                call_forest: forest,
                fee: 0,
                memo: None,
                valid_until: None,
                previous_receipt_hash: None,
                depends_on: vec![],
            };

            let result = executor.execute(&turn, &mut ledger);
            prop_assert!(result.is_committed(), "RefreshDelegation should succeed");

            // INVARIANT: After refresh, child's snapshot matches parent's CURRENT c-list.
            let parent_caps: Vec<CapabilityRef> = ledger
                .get(&parent_id)
                .unwrap()
                .capabilities
                .iter()
                .cloned()
                .collect();
            let child = ledger.get(&child_id).unwrap();
            let delegation = child.delegation.as_ref().unwrap();

            prop_assert_eq!(delegation.snapshot.len(), parent_caps.len(),
                "After refresh, snapshot length should match parent's c-list length");

            // Each capability in the snapshot should match what the parent holds.
            for (snap_cap, parent_cap) in delegation.snapshot.iter().zip(parent_caps.iter()) {
                prop_assert_eq!(snap_cap.target, parent_cap.target,
                    "Snapshot target mismatch");
                prop_assert_eq!(&snap_cap.permissions, &parent_cap.permissions,
                    "Snapshot permissions mismatch");
            }

            // INVARIANT: Child can never exercise capabilities wider than parent holds.
            for snap_cap in &delegation.snapshot {
                let parent_held = ledger
                    .get(&parent_id)
                    .unwrap()
                    .capabilities
                    .lookup_by_target(&snap_cap.target);
                prop_assert!(parent_held.is_some(),
                    "Child has capability to {:?} which parent doesn't hold", snap_cap.target);
                let parent_cap = parent_held.unwrap();
                prop_assert!(is_attenuation(&parent_cap.permissions, &snap_cap.permissions),
                    "Child capability {:?} is wider than parent's {:?}",
                    snap_cap.permissions, parent_cap.permissions);
            }
        }
    }
}

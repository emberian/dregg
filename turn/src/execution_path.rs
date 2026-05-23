//! Execution path routing: determines whether a turn can take the fast path
//! (single-owner, consensusless) or must go through consensus.
//!
//! The routing decision is based on two conditions:
//! 1. All cells in the write set must be owned solely by the turn's signer.
//! 2. The turn must have no cross-turn dependencies (`depends_on` is empty).
//!
//! If both conditions hold, the turn qualifies for the fast path. Otherwise,
//! it must be ordered via consensus to prevent double-spend and resolve conflicts.

use pyana_cell::Ledger;
use serde::{Deserialize, Serialize};

use crate::conflict::extract_access_sets;
use crate::turn::Turn;

/// The execution path a turn should take.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ExecutionPath {
    /// Single-owner fast path: the turn only touches cells owned by the signer.
    /// Can be executed immediately via certificate collection (2f+1 validator sigs)
    /// without running a full BFT consensus round.
    FastPath,
    /// Consensus path: the turn touches cells owned by multiple agents, or has
    /// cross-turn dependencies. Must be ordered via BFT consensus before execution.
    Consensus,
}

impl ExecutionPath {
    /// Returns true if this is the fast path.
    pub fn is_fast_path(&self) -> bool {
        matches!(self, ExecutionPath::FastPath)
    }

    /// Returns true if this requires consensus.
    pub fn is_consensus(&self) -> bool {
        matches!(self, ExecutionPath::Consensus)
    }
}

/// Compute the execution path for a turn given the current ledger state.
///
/// This inspects the turn's write set and checks:
/// 1. `turn.depends_on` is empty (no cross-turn dependencies)
/// 2. Every cell in the write set is owned by the turn's agent (same public_key)
///
/// If both conditions hold, returns `ExecutionPath::FastPath`.
/// Otherwise, returns `ExecutionPath::Consensus`.
///
/// Non-existent cells in the write set (from `CreateCell` effects) are allowed
/// on the fast path because the creator will own them by construction.
pub fn compute_execution_path(turn: &Turn, ledger: &Ledger) -> ExecutionPath {
    // Condition 1: No cross-turn dependencies.
    if !turn.depends_on.is_empty() {
        return ExecutionPath::Consensus;
    }

    // Look up the agent's public key from the ledger.
    let agent_public_key = match ledger.get(&turn.agent) {
        Some(cell) => cell.public_key,
        // Agent cell doesn't exist — cannot determine ownership, route to consensus.
        None => return ExecutionPath::Consensus,
    };

    // Extract the write set from the turn.
    let (_read_set, write_set) = extract_access_sets(turn);

    // Condition 2: All write-set cells must be owned by the turn's agent.
    for cell_id in &write_set {
        match ledger.get(cell_id) {
            Some(cell) => {
                if cell.public_key != agent_public_key {
                    return ExecutionPath::Consensus;
                }
            }
            // Non-existent cell (e.g., CreateCell target): allowed on fast path
            // because the new cell will be owned by the creator.
            None => continue,
        }
    }

    ExecutionPath::FastPath
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::action::{Action, Authorization, DelegationMode, Effect};
    use crate::forest::{CallForest, CallTree};
    use pyana_cell::{Cell, Preconditions};

    fn insert_cell(ledger: &mut Ledger, public_key: [u8; 32], balance: u64) -> CellId {
        let token_id = [0u8; 32];
        let cell = Cell::with_balance(public_key, token_id, balance);
        let id = cell.id;
        ledger.insert_cell(cell).unwrap();
        id
    }

    #[test]
    fn single_owner_gets_fast_path() {
        let mut ledger = Ledger::new();
        let pk = [1u8; 32];
        let agent_id = insert_cell(&mut ledger, pk, 1000);

        let turn = Turn {
            agent: agent_id,
            nonce: 0,
            call_forest: CallForest::new(),
            fee: 100,
            memo: None,
            valid_until: None,
            previous_receipt_hash: None,
            depends_on: vec![],
        };

        assert_eq!(
            compute_execution_path(&turn, &ledger),
            ExecutionPath::FastPath
        );
    }

    #[test]
    fn multi_owner_gets_consensus() {
        let mut ledger = Ledger::new();
        let pk_alice = [1u8; 32];
        let pk_bob = [2u8; 32];
        let alice_id = insert_cell(&mut ledger, pk_alice, 1000);
        let bob_id = insert_cell(&mut ledger, pk_bob, 1000);

        let action = Action {
            target: bob_id,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Signature([0u8; 32], [0u8; 32]),
            preconditions: Preconditions::default(),
            effects: vec![Effect::SetField {
                cell: bob_id,
                index: 0,
                value: [1u8; 32],
            }],
            may_delegate: DelegationMode::None,
            balance_change: None,
            commitment_mode: Default::default(),
        };

        let tree = CallTree {
            action,
            children: vec![],
            hash: [0u8; 32],
        };

        let turn = Turn {
            agent: alice_id,
            nonce: 0,
            call_forest: CallForest {
                roots: vec![tree],
                forest_hash: [0u8; 32],
            },
            fee: 100,
            memo: None,
            valid_until: None,
            previous_receipt_hash: None,
            depends_on: vec![],
        };

        assert_eq!(
            compute_execution_path(&turn, &ledger),
            ExecutionPath::Consensus
        );
    }

    #[test]
    fn dependencies_force_consensus() {
        let mut ledger = Ledger::new();
        let pk = [1u8; 32];
        let agent_id = insert_cell(&mut ledger, pk, 1000);

        let turn = Turn {
            agent: agent_id,
            nonce: 0,
            call_forest: CallForest::new(),
            fee: 100,
            memo: None,
            valid_until: None,
            previous_receipt_hash: None,
            depends_on: vec![[0xaa; 32]],
        };

        assert_eq!(
            compute_execution_path(&turn, &ledger),
            ExecutionPath::Consensus
        );
    }
}

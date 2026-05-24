//! Strategies for generating fully-formed [`pyana_turn::Turn`] values that
//! the executor will accept.
//!
//! A "valid-shaped" turn is one where:
//! 1. The agent cell exists in the ledger.
//! 2. The nonce matches the agent's current nonce.
//! 3. Authorization is `Unchecked` (we pair this with `AuthRequired::None`
//!    permissions in the open ledger so authorization is satisfied without
//!    real signatures).
//! 4. Targets exist; capability lookups will resolve; preconditions are
//!    empty (defaulted) so they don't reject.
//! 5. Fee is zero (so we don't have to model fee economics in the
//!    invariant).
//!
//! The `previous_receipt_hash` is set by the test harness as it builds a
//! chain — we don't try to bake chain ordering into the strategy itself
//! because the chain is a sequential construction, not a random one.

use std::collections::HashMap;

use proptest::prelude::*;
use pyana_cell::CellId;
use pyana_turn::{
    Action, Authorization, CallForest, DelegationMode, Effect, turn::Turn,
};

/// A single transfer operation described abstractly, before being projected
/// into a `Turn`.
#[derive(Clone, Debug)]
pub struct TransferOp {
    /// Index into the test's `ids` vector.
    pub from_idx: usize,
    /// Index into the test's `ids` vector.
    pub to_idx: usize,
    /// Amount in computrons.
    pub amount: u64,
}

/// Strategy: an `Op` with indices in `[0, n_cells)` and a bounded amount.
pub fn arb_transfer_op(n_cells: usize, max_amount: u64) -> impl Strategy<Value = TransferOp> {
    (0..n_cells, 0..n_cells, 1u64..=max_amount).prop_map(|(from_idx, to_idx, amount)| TransferOp {
        from_idx,
        to_idx,
        amount,
    })
}

/// Strategy: a non-empty sequence of `TransferOp`s.
pub fn arb_transfer_ops(
    n_cells: usize,
    max_amount: u64,
    max_ops: usize,
) -> impl Strategy<Value = Vec<TransferOp>> {
    proptest::collection::vec(arb_transfer_op(n_cells, max_amount), 1..=max_ops)
}

/// Build a one-action turn that executes a single `Transfer` effect.
///
/// `nonce` MUST equal the agent cell's current nonce or the executor will
/// reject the turn. `previous_receipt_hash` should be set when chaining
/// multiple turns from the same agent; pass `None` for the first turn.
pub fn build_transfer_turn(
    from: CellId,
    to: CellId,
    amount: u64,
    nonce: u64,
    previous_receipt_hash: Option<[u8; 32]>,
) -> Turn {
    let mut forest = CallForest::new();
    let action = Action {
        target: from,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![Effect::Transfer { from, to, amount }],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
    };
    forest.add_root(action);

    Turn {
        agent: from,
        nonce,
        call_forest: forest,
        fee: 0,
        memo: None,
        valid_until: None,
        previous_receipt_hash,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
    }
}

/// Build a one-action turn that does nothing (no effects, target=self,
/// `Authorization::Unchecked`). Useful for nonce / receipt-chain tests
/// where the only thing under examination is the agent's bookkeeping.
pub fn build_no_op_turn(
    agent: CellId,
    nonce: u64,
    previous_receipt_hash: Option<[u8; 32]>,
) -> Turn {
    let mut forest = CallForest::new();
    let action = Action {
        target: agent,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
    };
    forest.add_root(action);

    Turn {
        agent,
        nonce,
        call_forest: forest,
        fee: 0,
        memo: None,
        valid_until: None,
        previous_receipt_hash,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
    }
}

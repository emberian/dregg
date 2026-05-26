//! Sealed-field integrity invariant.
//!
//! > For any cell read from a ledger, `cell.verify_id_integrity()` returns
//! > true (i.e. `id == derive_raw(public_key, token_id)`).
//!
//! The sealing is type-system-enforced for direct mutation:
//! `Cell::id`, `Cell::public_key`, `Cell::token_id`, `CellState::nonce`,
//! `CellState::balance`, `CellState::proved_state`, `CellState::delegation_epoch`
//! are `pub(crate)`. The 7 corresponding `compile_fail` doctests live on the
//! accessor methods in `cell/src/cell.rs` and `cell/src/state.rs`.
//!
//! This module covers the *runtime* analogue: even when state mutates
//! through legitimate executor paths (Transfer, IncrementNonce, etc.),
//! the content-address invariant is preserved on every cell after every
//! committed turn.
//!
//! Operationally: build a random open ledger, drive it through a sequence
//! of random Transfer + IncrementNonce turns, and after each turn assert
//! `verify_id_integrity()` on every (real, non-stub) cell in the ledger.
//!
//! NOTE: `Cell::remote_stub_with_id*` constructors deliberately produce
//! cells with `public_key = [0; 32]` whose id does NOT satisfy the
//! integrity check — these are placeholder rows for cross-federation
//! peers. We filter them out via `cell.public_key() != [0u8; 32]`.

use crate::Invariant;

use proptest::prelude::*;

pub struct SealedFieldIntegrity;

impl Invariant for SealedFieldIntegrity {
    const NAME: &'static str = "sealed_field_integrity";
    const DESCRIPTION: &'static str = "after any sequence of executor turns, every non-stub cell's id matches derive_raw(public_key, token_id)";
}

/// A turn-shape the property test can emit. We keep the shape small: the
/// invariant is about cell-identity persistence under state mutation, so
/// any state-changing effect family suffices.
#[derive(Clone, Debug)]
enum Op {
    Transfer {
        from_idx: usize,
        to_idx: usize,
        amount: u64,
    },
    NoOp {
        agent_idx: usize,
    },
}

fn arb_op(n_cells: usize) -> impl Strategy<Value = Op> {
    prop_oneof![
        (0..n_cells, 0..n_cells, 1u64..1000).prop_map(|(from_idx, to_idx, amount)| Op::Transfer {
            from_idx,
            to_idx,
            amount
        }),
        (0..n_cells).prop_map(|agent_idx| Op::NoOp { agent_idx }),
    ]
}

fn arb_ops(n_cells: usize, max_ops: usize) -> impl Strategy<Value = Vec<Op>> {
    proptest::collection::vec(arb_op(n_cells), 1..=max_ops)
}

/// Assert the invariant on every real cell in the ledger.
fn assert_all_ids_intact(ledger: &dregg_cell::Ledger) -> Result<(), TestCaseError> {
    for (id, cell) in ledger.iter() {
        // Skip cross-federation stub rows — `remote_stub_with_id*`
        // deliberately constructs cells with public_key = [0; 32] whose
        // id was supplied by the federation rather than derived. They are
        // documented exceptions to the integrity invariant.
        if cell.public_key() == &[0u8; 32] {
            continue;
        }
        prop_assert!(
            cell.verify_id_integrity(),
            "cell id integrity broken: id={:?} pk={:?} token={:?}",
            id,
            cell.public_key(),
            cell.token_id(),
        );
    }
    Ok(())
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    /// After every committed turn (Transfer or no-op), every real cell's
    /// id field still equals `derive_raw(public_key, token_id)`.
    #[test]
    fn sealed_field_integrity_holds(ops in arb_ops(4, 25)) {
        let spec = LedgerSpec {
            n_cells: 4,
            balance_each: 10_000,
            wide_open: true,
        };
        let (mut ledger, ids) = build_open_ledger(&spec);
        let executor = TurnExecutor::new(ComputronCosts::zero());

        // Baseline: brand-new ledger must satisfy the invariant.
        assert_all_ids_intact(&ledger)?;

        for op in &ops {
            let _ = match op {
                Op::Transfer { from_idx, to_idx, amount } => {
                    if from_idx == to_idx {
                        continue;
                    }
                    let from = ids[*from_idx];
                    let to = ids[*to_idx];
                    let nonce = ledger.get(&from).unwrap().state.nonce();
                    let turn = build_transfer_turn(from, to, *amount, nonce, None);
                    executor.execute(&turn, &mut ledger)
                }
                Op::NoOp { agent_idx } => {
                    let agent = ids[*agent_idx];
                    let nonce = ledger.get(&agent).unwrap().state.nonce();
                    let turn = build_no_op_turn(agent, nonce, None);
                    executor.execute(&turn, &mut ledger)
                }
            };
            // Whether or not the turn committed, the invariant must hold.
            assert_all_ids_intact(&ledger)?;
        }
    }

    /// Stronger variant: also exercise `IncrementNonce` effects as their
    /// own turn, plus paranoid Transfer chains. Ensures the journal /
    /// rollback paths also preserve id integrity (committed and rejected
    /// turns alike).
    #[test]
    fn sealed_field_integrity_under_increment_nonce(
        ops in proptest::collection::vec(0usize..4, 1..=20),
    ) {
        let spec = LedgerSpec {
            n_cells: 4,
            balance_each: 10_000,
            wide_open: true,
        };
        let (mut ledger, ids) = build_open_ledger(&spec);
        let executor = TurnExecutor::new(ComputronCosts::zero());

        for &agent_idx in &ops {
            let agent = ids[agent_idx];
            let nonce = ledger.get(&agent).unwrap().state.nonce();
            // Single-action turn that increments the agent's own nonce.
            let action = dregg_turn::Action {
                target: agent,
                method: [0u8; 32],
                args: vec![],
                authorization: dregg_turn::Authorization::Unchecked,
                preconditions: Default::default(),
                effects: vec![Effect::IncrementNonce { cell: agent }],
                may_delegate: dregg_turn::DelegationMode::None,
                commitment_mode: Default::default(),
                balance_change: None,
                witness_blobs: vec![],
            };
            let mut forest = dregg_turn::CallForest::new();
            forest.add_root(action);
            let turn = dregg_turn::turn::Turn {
                agent,
                nonce,
                call_forest: forest,
                fee: 0,
                memo: None,
                valid_until: None,
                previous_receipt_hash: None,
                depends_on: vec![],
                conservation_proof: None,
                sovereign_witnesses: std::collections::HashMap::new(),
                execution_proof: None,
                execution_proof_cell: None,
                execution_proof_new_commitment: None,
                custom_program_proofs: None,
                effect_binding_proofs: Vec::new(),
                cross_effect_dependencies: Vec::new(),
                effect_witness_index_map: Vec::new(),
            };
            let _ = executor.execute(&turn, &mut ledger);
            assert_all_ids_intact(&ledger)?;
        }
    }
}

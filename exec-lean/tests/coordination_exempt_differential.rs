//! COORDINATION-TURN CLASS Lean/Rust differential ("leash, not ledger").
//!
//! The `ComputronCosts::coordination_exempt` class is ADMISSION-ONLY: it waives
//! the CHARGE for EmitEvent-only turns (`Turn::is_coordination`) so a `fee = 0`
//! coordination turn admits under REAL (non-zero) computron costs. `fee = 0` is
//! the shape every prior Lean/Rust differential already locked (see
//! `faucet_fee_well_divergence.rs`: "Every prior differential used `fee == 0`"),
//! so exempting the class must introduce NO producer divergence — the state
//! transition of a committed fee=0 EmitEvent turn is untouched; only the Rust
//! admission gate changed. This test pins that: the SAME fee=0 chat turn, run
//! through the exempt Rust executor (default costs — which would REJECT it
//! without the exemption) and through the verified Lean producer, commits on
//! both and agrees cell-by-cell + on `.root()`.
//!
//! Mirrors the `faucet_fee_well_divergence.rs` harness (open cells,
//! `execute_via_lean`, `ledgers_agree`). Requires the linked Lean archive
//! (`lean-shadow` + `lean_available()`); self-skips when absent (PANICS under
//! `DREGG_TEST_REQUIRE_LEAN=1`).

use dregg_cell::permissions::AuthRequired;
use dregg_cell::{Cell, CellId, Ledger, Permissions};
use dregg_exec_lean::lean_apply::execute_via_lean;
use dregg_exec_lean::lean_shadow::ShadowHostCtx;
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, Event, TurnExecutor,
    turn::Turn,
};
use std::collections::HashMap;

fn open_permissions() -> Permissions {
    Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

fn make_open_cell(seed: u8, balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37);
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell
}

/// An EmitEvent-only "chat" turn — the coordination shape, `fee = 0`.
fn chat_turn(agent: CellId, payload: &[u8]) -> Turn {
    let data = payload
        .chunks(8)
        .map(|chunk| {
            let mut word = [0u8; 32];
            word[24..24 + chunk.len()].copy_from_slice(chunk);
            word
        })
        .collect();
    let mut forest = CallForest::new();
    forest.add_root(Action {
        target: agent,
        method: *blake3::hash(b"helm.chat").as_bytes(),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![Effect::EmitEvent {
            cell: agent,
            event: Event::new(*blake3::hash(b"helm.chat").as_bytes(), data),
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    });
    Turn {
        agent,
        nonce: 0,
        call_forest: forest,
        fee: 0,
        memo: None,
        valid_until: Some(1_000_000),
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    }
}

fn skip_no_lean() -> bool {
    !dregg_lean_ffi::demand_lean(
        dregg_lean_ffi::lean_available(),
        "Lean archive (lean_available)",
    )
}

/// Compare two ledgers cell-by-cell (balance + nonce + leaf commitment) AND on `.root()`.
fn ledgers_agree(
    rust: &mut Ledger,
    lean: &mut Ledger,
    ids: &[(&str, CellId)],
) -> Result<(), String> {
    for (name, id) in ids {
        let r = rust
            .get(id)
            .ok_or_else(|| format!("cell {name} missing from RUST ledger"))?;
        let l = lean
            .get(id)
            .ok_or_else(|| format!("cell {name} missing from LEAN ledger"))?;
        if r.state.balance() != l.state.balance() {
            return Err(format!(
                "balance divergence on {name}: rust={} lean={}",
                r.state.balance(),
                l.state.balance()
            ));
        }
        if r.state.nonce() != l.state.nonce() {
            return Err(format!(
                "nonce divergence on {name}: rust={} lean={}",
                r.state.nonce(),
                l.state.nonce()
            ));
        }
        let rc = dregg_cell::compute_canonical_state_commitment(r);
        let lc = dregg_cell::compute_canonical_state_commitment(l);
        if rc != lc {
            return Err(format!(
                "LEAF commitment divergence on {name}: rust={rc:?} lean={lc:?}"
            ));
        }
    }
    let rr = rust.root();
    let lr = lean.root();
    if rr != lr {
        return Err(format!("ROOT divergence: rust={rr:?} lean={lr:?}"));
    }
    Ok(())
}

/// THE CLASS DIFFERENTIAL: a fee=0 EmitEvent-only chat turn from an UNFUNDED
/// cell, admitted by the EXEMPT Rust executor under REAL costs, agrees with the
/// verified Lean producer on full state + `.root()`.
#[test]
fn zero_fee_coordination_turn_agrees_across_producers() {
    if skip_no_lean() {
        return;
    }
    // UNFUNDED agent: balance 0 — the class's whole point (fleet comms cells
    // need no faucet round-trip at all).
    let agent = make_open_cell(3, 0);
    let agent_id = agent.id();
    let mut pre = Ledger::new();
    pre.insert_cell(agent).unwrap();

    let turn = chat_turn(agent_id, b"gm from the leash");

    // RUST: REAL default costs + the exemption. Without `coordination_exempt`
    // this exact turn REJECTS BudgetExceeded (locked in
    // `turn/tests/coordination_fee_exempt.rs`); with it, it commits.
    let mut costs = ComputronCosts::default_costs();
    costs.coordination_exempt = true;
    let executor = TurnExecutor::new(costs);
    let mut rust_ledger = pre.clone();
    let rust_result = executor.execute(&turn, &mut rust_ledger);
    assert!(
        rust_result.is_committed(),
        "exempt Rust executor must commit the fee=0 chat turn: {rust_result:?}"
    );

    // LEAN: the verified producer on the SAME turn. fee=0 is the historically
    // locked differential shape — the exemption changes Rust ADMISSION only,
    // so the producers must agree exactly.
    let host = ShadowHostCtx {
        block_height: 0,
        ..ShadowHostCtx::diag()
    };
    let (mut lean_ledger, lean_committed) = execute_via_lean(&turn, &pre, &host)
        .unwrap_or_else(|e| panic!("Lean producer errored: {e}"));
    assert!(
        lean_committed,
        "commit-bit divergence: Rust committed, Lean did not"
    );

    let ids = [("agent", agent_id)];
    if let Err(e) = ledgers_agree(&mut rust_ledger, &mut lean_ledger, &ids) {
        panic!("coordination-class differential diverged: {e}");
    }
}

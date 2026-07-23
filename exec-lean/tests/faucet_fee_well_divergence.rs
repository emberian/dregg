//! faucet_fee_well_divergence.rs — REPRODUCE + LOCK the n=5 dogfood faucet divergence.
//!
//! The live n=5 node logged `lean_root ≠ rust_root` on a faucet `Transfer` turn (the verified Lean
//! executor authoritative + committed; the demoted Rust reference produced a DIFFERENT state root).
//! This file reproduces that turn shape — a faucet `Transfer` carrying a NON-ZERO `fee` with a FEE
//! WELL configured (THE EPOCH §5, exactly as `configure_turn_executor` does on every node) — and
//! asserts the two producers AGREE on full per-cell state + `.root()` after the fix.
//!
//! # The bug
//!
//! Every faucet turn carries a `fee` (sized to the computron cost). After a committing turn the Rust
//! executor (a) DEBITS the agent the fee in its prologue and (b) MOVES the fee to the real fee-well
//! cell (`distribute_fee_shares`). The verified Lean producer reconstituted NEITHER: the kernel
//! debits the fee onto the agent's RECORD scalar (the extractor reads the per-asset `bal` table) and
//! distributes to FIXED PLACEHOLDER cells (`admCtxOfHost`'s 0xF00/0xF01) + burns the residue (the
//! real fee policy is host config the wire grammar does not carry). So the reconstituted ledger
//! carried neither the agent's fee debit nor the fee-well credit, and `rust_root ≠ lean_root` for
//! any fee-bearing turn. Every prior differential used `fee == 0`, so the gap stayed latent until
//! the n=5 dogfood ran with real fees. The fix replays the host's real fee move
//! (`lean_apply::apply_fee_distribution`) onto the reconstituted ledger, gated on the verified
//! commit bit — so both producers reflect the identical host fee policy WITHOUT changing the Lean
//! spec (whose placeholder fee accounting is the host-policy seam, not deployed-cell semantics).
//!
//! Mirrors the stable `lean_state_producer_widen` harness (`execute_via_lean` + a separate Rust
//! `TurnExecutor` + cell-by-cell agreement), extended with a non-zero fee + a configured fee well.
//!
//! Requires the linked Lean archive (`lean-shadow` + `lean_available()`); self-skips when absent (PANICS under `DREGG_TEST_REQUIRE_LEAN=1`).

use std::collections::HashMap;

use dregg_cell::permissions::AuthRequired;
use dregg_cell::{Cell, CellId, Ledger, Permissions};
use dregg_exec_lean::lean_apply::{ProducerOutcome, execute_via_lean, produce_via_lean};
use dregg_exec_lean::lean_shadow::ShadowHostCtx;
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, Event, TurnExecutor,
    turn::Turn,
};

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

fn transfer_turn(agent: CellId, from: CellId, to: CellId, amount: u64, fee: u64) -> Turn {
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
        witness_blobs: vec![],
    };
    forest.add_root(action);
    Turn {
        agent,
        nonce: 0,
        call_forest: forest,
        fee,
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

fn chat_turn(agent: CellId, payload: &[u8], fee: u64) -> Turn {
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
        fee,
        memo: Some(String::from_utf8(payload.to_vec()).expect("test payload is UTF-8")),
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

fn assert_producer_agreed(outcome: ProducerOutcome, label: &str) {
    match outcome {
        ProducerOutcome::LeanAuthoritative {
            committed,
            rust_agreed,
            lean_root,
            rust_root,
            rust_committed,
        } => {
            assert!(committed, "Lean must commit the {label}");
            assert!(rust_committed, "Rust must commit the {label}");
            assert!(
                rust_agreed,
                "Lean/Rust authority divergence on {label}: lean_root={lean_root:?} rust_root={rust_root:?}"
            );
            assert_eq!(lean_root, rust_root, "root agreement on {label}");
        }
        ProducerOutcome::Fallback { reason } => {
            panic!("{label} escaped the verified producer through fallback: {reason}")
        }
    }
}

fn skip_no_lean() -> bool {
    !dregg_lean_ffi::demand_lean(
        dregg_lean_ffi::lean_available(),
        "Lean archive (lean_available)",
    )
}

/// Compare two ledgers cell-by-cell (balance + nonce) AND on `.root()` for the given ids.
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
                "LEAF commitment divergence on {name} (balances/nonces equal): rust={rc:?} lean={lc:?}"
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

/// Run a faucet-shaped `Transfer` at `block_height` (amount + `fee`, with a fee well configured)
/// through both producers and return `Ok(())` on full agreement (state + `.root()`), else the first
/// divergence. Mirrors `lean_state_producer_widen::diff`, threading the fee well + a non-zero fee +
/// the host chain height. At `block_height > 0` this also exercises the PI-v3 committed-height stamp.
fn run_faucet_at(amount: u64, fee: u64, block_height: u64) -> Result<(), String> {
    let faucet = make_open_cell(1, 1_000_000);
    let recipient = make_open_cell(2, 0);
    let fee_well = make_open_cell(9, 0);
    let faucet_id = faucet.id();
    let recipient_id = recipient.id();
    let fee_well_id = fee_well.id();

    let mut pre = Ledger::new();
    pre.insert_cell(faucet).unwrap();
    pre.insert_cell(recipient).unwrap();
    pre.insert_cell(fee_well).unwrap();

    let turn = transfer_turn(faucet_id, faucet_id, recipient_id, amount, fee);

    // RUST reference: zero computron costs + a fee well + the chain height set to `block_height`
    // (the executor stamps `committed_height = self.block_height` onto every forest-touched cell).
    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_fee_well_cell(fee_well_id);
    executor.set_block_height(block_height);
    let mut rust_ledger = pre.clone();
    let rust_result = executor.execute(&turn, &mut rust_ledger);
    if !rust_result.is_committed() {
        return Err(format!("Rust executor did not commit: {rust_result:?}"));
    }

    // LEAN producer: the host ctx carries the SAME fee well AND the SAME block height, so the
    // reconstitution replays the identical host fee move + committed-height stamp.
    let host = ShadowHostCtx {
        block_height,
        fee_well_cell: Some(fee_well_id),
        ..ShadowHostCtx::diag()
    };
    let (mut lean_ledger, lean_committed) =
        execute_via_lean(&turn, &pre, &host).map_err(|e| format!("Lean producer errored: {e}"))?;
    if !lean_committed {
        return Err("commit-bit divergence: Rust committed, Lean did not".to_string());
    }

    let ids = [
        ("faucet", faucet_id),
        ("recipient", recipient_id),
        ("fee_well", fee_well_id),
    ];
    ledgers_agree(&mut rust_ledger, &mut lean_ledger, &ids)?;

    // Pin the committed-height stamp on both forest-touched cells (source + dest), matching Rust.
    if block_height != 0 {
        for (name, id) in [("faucet", faucet_id), ("recipient", recipient_id)] {
            let h = lean_ledger.get(&id).unwrap().state.committed_height();
            if h != block_height {
                return Err(format!(
                    "committed_height not stamped on {name}: got {h}, want {block_height}"
                ));
            }
        }
        // The fee well is a Phase-3 recipient (credited AFTER the committed-height loop), so it is
        // NOT stamped — its height stays at the pre-state 0 in BOTH producers.
        let wh = lean_ledger
            .get(&fee_well_id)
            .unwrap()
            .state
            .committed_height();
        if wh != 0 {
            return Err(format!(
                "fee well was stamped with committed_height {wh} (should stay 0 — it is a \
                 Phase-3 fee recipient, not a forest-touched cell)"
            ));
        }
    }
    Ok(())
}

/// Run a faucet-shaped `Transfer` (amount + `fee`, with a fee well configured) through both
/// producers and return `Ok(())` on full agreement (state + `.root()`), else the first divergence.
/// Mirrors `lean_state_producer_widen::diff`, threading the fee well + a non-zero fee.
fn run_faucet(amount: u64, fee: u64) -> Result<(), String> {
    let faucet = make_open_cell(1, 1_000_000);
    let recipient = make_open_cell(2, 0);
    let fee_well = make_open_cell(9, 0);
    let faucet_id = faucet.id();
    let recipient_id = recipient.id();
    let fee_well_id = fee_well.id();

    let mut pre = Ledger::new();
    pre.insert_cell(faucet).unwrap();
    pre.insert_cell(recipient).unwrap();
    pre.insert_cell(fee_well).unwrap();

    let turn = transfer_turn(faucet_id, faucet_id, recipient_id, amount, fee);

    // RUST reference: zero computron costs (so the fee-as-budget cap never trips) + a fee well —
    // THE EPOCH §5 fee config every node installs. Block height 0 matches the n=5 devnet
    // (`latest_height: 0`), so the `committed_height` commitment limb (stamped only when
    // `block_height != old_height`) stays 0 on both sides and the FEE is the sole divergence —
    // exactly the reported faucet bug. (The height>0 `committed_height` reconstitution is a
    // separate, broader matter, moot at devnet height 0.)
    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_fee_well_cell(fee_well_id);
    let mut rust_ledger = pre.clone();
    let rust_result = executor.execute(&turn, &mut rust_ledger);
    if !rust_result.is_committed() {
        return Err(format!("Rust executor did not commit: {rust_result:?}"));
    }

    // LEAN producer: the host ctx carries the SAME fee well (the seam the fix threads) so the
    // reconstitution replays the identical host fee move.
    let host = ShadowHostCtx {
        block_height: 0,
        fee_well_cell: Some(fee_well_id),
        ..ShadowHostCtx::diag()
    };
    let (mut lean_ledger, lean_committed) =
        execute_via_lean(&turn, &pre, &host).map_err(|e| format!("Lean producer errored: {e}"))?;
    if !lean_committed {
        return Err("commit-bit divergence: Rust committed, Lean did not".to_string());
    }

    let ids = [
        ("faucet", faucet_id),
        ("recipient", recipient_id),
        ("fee_well", fee_well_id),
    ];
    ledgers_agree(&mut rust_ledger, &mut lean_ledger, &ids)?;

    // Pin the EPOCH §5 post-state explicitly (the fee MOVED to the well; conserved).
    let well = lean_ledger.get(&fee_well_id).unwrap().state.balance();
    if well != fee as i64 {
        return Err(format!(
            "fee well not credited the fee: well={well} fee={fee}"
        ));
    }
    Ok(())
}

/// THE FAUCET TURN: a fee-bearing `Transfer` with a fee well — the n=5 dogfood divergence. Before
/// the fix this returned a `ROOT divergence` (the agent fee debit + fee-well credit were dropped by
/// the reconstitution); after the fix both producers agree on full state + `.root()`.
#[test]
fn faucet_transfer_with_fee_well_agrees() {
    if skip_no_lean() {
        return;
    }
    run_faucet(100, 297).expect("faucet transfer with a fee well must agree (state + .root())");
}

/// The zero-fee transfer must STILL agree (the fix is a no-op at `fee == 0`) — guards against the
/// fee replay perturbing the long-standing zero-fee round-trip.
#[test]
fn zero_fee_transfer_still_agrees() {
    if skip_no_lean() {
        return;
    }
    run_faucet(100, 0).expect("zero-fee transfer must still agree");
}

/// A range of fees agrees — the fix is the same deterministic host-policy replay for any fee.
#[test]
fn fee_family_agrees() {
    if skip_no_lean() {
        return;
    }
    for fee in [1u64, 10, 100, 1000, 9999] {
        run_faucet(100, fee).unwrap_or_else(|e| panic!("fee={fee} must agree: {e}"));
    }
}

/// THE SWAP AUTHORITY-INVERSION GOLDEN (agents `4a8882bb` / `12d4e7e6`, live cross-machine mesh):
/// a fee-bearing `Transfer` at a NON-ZERO chain height. The Rust executor stamps
/// `committed_height = block_height` onto every forest-touched cell (source + dest) and folds it into
/// the canonical commitment; the verified-Lean producer's `WireState → Ledger` extractor DROPPED that
/// host-stamped limb (the kernel models no committed-height column), so `lean_root != rust_root` for
/// EVERY committing covered turn at height > 0 — surfacing as "THE SWAP authority inversion" under
/// cross-machine reorg (covered turns re-executed at real heights). Mirrors the funded-client payoff
/// shape (`node/tests/payoff_client_turn.rs`): amount 1000, fee 5000, off a funded balance.
///
/// FAILS BEFORE the fix with `ROOT divergence` (the committed-height stamp missing on the Lean side);
/// PASSES AFTER — the `apply_committed_height` replay stamps the identical host height on the same
/// forest-touched cells. The `fee_transfer_with_fee_well_agrees` zero-height sibling proves the fix is
/// a no-op at height 0 (so this is the NON-VACUOUS delta: same turn, only the height differs).
#[test]
fn swap_inversion_committed_height_transfer_agrees() {
    if skip_no_lean() {
        return;
    }
    // The exact payoff shape (funded client Transfer: amount 1000, fee 5000) at a live chain height.
    run_faucet_at(1_000, 5_000, 4_812).expect(
        "THE SWAP authority-inversion golden: a fee-bearing Transfer at block_height > 0 must agree \
         on state + .root() (the committed-height stamp must be replayed on the Lean side)",
    );
}

/// The committed-height replay is the SAME deterministic host stamp across a range of heights and
/// fees — pins that the fix is not height-0-specific and never re-introduces the divergence.
#[test]
fn committed_height_family_agrees() {
    if skip_no_lean() {
        return;
    }
    for height in [1u64, 2, 100, 65_536, 1_000_000] {
        for fee in [0u64, 297, 5_000] {
            run_faucet_at(1_000, fee, height)
                .unwrap_or_else(|e| panic!("height={height} fee={fee} must agree: {e}"));
        }
    }
}

/// Regression for the shared-chat starvation incident. The signer already existed with only 90
/// computrons, so treating `found:true` as "funded" left every later chat turn permanently rejected.
/// Prove the owner faucet can commit a top-up INTO that existing cell, the authoritative balance
/// rises to 5,000, and the exact next metered chat-sized `EmitEvent` then commits. Both commits stay
/// on the verified producer and require full Lean/Rust verdict + root agreement.
#[test]
fn low_balance_recipient_top_up_commits_then_chat_send_commits() {
    if skip_no_lean() {
        return;
    }

    let faucet = make_open_cell(1, 1_000_000);
    let recipient = make_open_cell(2, 90);
    let fee_well = make_open_cell(9, 0);
    let faucet_id = faucet.id();
    let recipient_id = recipient.id();
    let fee_well_id = fee_well.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(faucet).unwrap();
    ledger.insert_cell(recipient).unwrap();
    ledger.insert_cell(fee_well).unwrap();

    let payload = b"This next chat-sized send must commit after the faucet top-up has actually raised the existing cell balance.";
    let costs = ComputronCosts::default();
    let mut chat = chat_turn(recipient_id, payload, 0);
    chat.fee = TurnExecutor::new(costs.clone()).estimate_cost(&chat);
    assert!(
        chat.fee > 90 && chat.fee < 5_000,
        "test must be load-bearing: chat fee {} must exceed the depleted balance but fit after top-up",
        chat.fee
    );
    let mut depleted = ledger.clone();
    let rejected = TurnExecutor::new(costs.clone()).execute(&chat, &mut depleted);
    assert!(
        !rejected.is_committed(),
        "depleted precondition must genuinely reject the chat turn: {rejected:?}"
    );

    let top_up = transfer_turn(faucet_id, faucet_id, recipient_id, 4_910, 0);
    let top_up_executor = TurnExecutor::new(ComputronCosts::zero());
    let (top_up_result, top_up_outcome) = produce_via_lean(&top_up_executor, &top_up, &mut ledger);
    assert!(top_up_result.is_committed(), "faucet top-up must commit");
    assert_producer_agreed(top_up_outcome, "existing-recipient faucet top-up");
    assert_eq!(
        ledger.get(&recipient_id).unwrap().state.balance(),
        5_000,
        "committed top-up must raise the existing recipient balance"
    );

    let mut chat_executor = TurnExecutor::new(costs);
    chat_executor.set_fee_well_cell(fee_well_id);
    let (chat_result, chat_outcome) = produce_via_lean(&chat_executor, &chat, &mut ledger);
    assert!(
        chat_result.is_committed(),
        "post-top-up chat send must commit"
    );
    assert_producer_agreed(chat_outcome, "post-top-up chat send");
    assert!(
        ledger.get(&recipient_id).unwrap().state.balance() < 5_000,
        "chat turn must really execute and spend its fee"
    );
    assert_eq!(
        ledger.get(&fee_well_id).unwrap().state.balance(),
        chat.fee as i64,
        "the committed chat fee must reach the configured fee well"
    );
}

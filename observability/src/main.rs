//! `pyana-observability` — turn execution + proof generation trace emitter.
//!
//! This is the **seed crate** for the in-browser turn explorer. It:
//!
//! 1. Constructs a minimal realistic Turn (single `Transfer` effect).
//! 2. Runs the executor on an in-memory ledger.
//! 3. Inspects pre/post cell state via the public ledger API.
//! 4. Projects the Turn's effects into the Effect VM's per-cell effect stream
//!    (duplicating the executor's private `convert_turn_effects_to_vm` projection
//!    rather than widening visibility on production code).
//! 5. Runs `generate_effect_vm_trace` + `stark::prove` + `stark::verify`.
//! 6. Emits a single JSON document covering all of the above to stdout.
//!
//! The emitted JSON is intended as the wire format an off-line explorer would
//! consume. It is **not** the executor's internal trace stream — that would
//! require instrumenting `executor.rs` itself (a separate, larger lift).

use pyana_cell::{
    AuthRequired, Cell, CellId, Ledger, Permissions, state::FIELD_ZERO,
};
use pyana_circuit::{
    EffectVmAir,
    effect_vm::{self, generate_effect_vm_trace},
    field::BabyBear,
    stark,
};
use pyana_turn::{
    ComputronCosts, DelegationMode, Effect, TurnBuilder, TurnExecutor, TurnResult,
};
use serde::Serialize;
use serde_json::{Value, json};

fn hex32(bytes: &[u8; 32]) -> String {
    hex::encode(bytes)
}

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

fn make_cell(seed: u8, balance: u64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    let token_id = [0u8; 32];
    let mut cell = Cell::with_balance(pk, token_id, balance);
    cell.permissions = open_permissions();
    cell
}

/// Capture the per-cell, per-Turn `Effect` snapshot. Mirrors only the
/// fields meaningful for a Transfer (the demo case); a full implementation
/// would re-render every effect variant.
#[derive(Serialize)]
struct EffectView {
    action_index: usize,
    kind: &'static str,
    from: Option<String>,
    to: Option<String>,
    amount: Option<u64>,
}

fn render_effects(turn: &pyana_turn::Turn) -> Vec<EffectView> {
    let mut out = Vec::new();
    for (i, tree) in turn.call_forest.roots.iter().enumerate() {
        for effect in &tree.action.effects {
            match effect {
                Effect::Transfer { from, to, amount } => out.push(EffectView {
                    action_index: i,
                    kind: "Transfer",
                    from: Some(hex32(from.as_bytes())),
                    to: Some(hex32(to.as_bytes())),
                    amount: Some(*amount),
                }),
                other => out.push(EffectView {
                    action_index: i,
                    kind: variant_name(other),
                    from: None,
                    to: None,
                    amount: None,
                }),
            }
        }
    }
    out
}

fn variant_name(effect: &Effect) -> &'static str {
    match effect {
        Effect::Transfer { .. } => "Transfer",
        Effect::SetField { .. } => "SetField",
        Effect::GrantCapability { .. } => "GrantCapability",
        Effect::RevokeCapability { .. } => "RevokeCapability",
        Effect::IncrementNonce { .. } => "IncrementNonce",
        _ => "Other",
    }
}

/// Project a Turn's effects into the Effect VM's `Effect` stream from the
/// perspective of one cell.
///
/// **Duplicated** from `pyana_turn::executor::TurnExecutor::convert_turn_effects_to_vm`
/// (which is a private helper). Widening visibility on the production executor
/// would force the trust-critical entry point's call shape to depend on an
/// observability concern; copying the projection keeps the executor untouched.
/// The trade-off: a future "any-turn trace" tool must keep these projections in
/// lockstep (see README for follow-up).
fn project_turn_effects_for_cell(
    turn: &pyana_turn::Turn,
    cell_id: &CellId,
) -> Vec<effect_vm::Effect> {
    use pyana_turn::forest::CallTree;

    fn walk(
        tree: &CallTree,
        cell_id: &CellId,
        out: &mut Vec<effect_vm::Effect>,
    ) {
        for effect in &tree.action.effects {
            match effect {
                Effect::Transfer { from, to, amount } => {
                    if from == cell_id {
                        out.push(effect_vm::Effect::Transfer {
                            amount: *amount,
                            direction: 1,
                        });
                    } else if to == cell_id {
                        out.push(effect_vm::Effect::Transfer {
                            amount: *amount,
                            direction: 0,
                        });
                    }
                }
                _ => {
                    // Demo intentionally narrowed to Transfer; the production
                    // projection handles the full effect set.
                }
            }
        }
        for child in &tree.children {
            walk(child, cell_id, out);
        }
    }

    let mut out = Vec::new();
    for tree in &turn.call_forest.roots {
        walk(tree, cell_id, &mut out);
    }
    out
}

fn cell_state_view(label: &str, ledger: &Ledger, id: &CellId) -> Value {
    let cell = ledger.get(id).expect("cell missing");
    let fields: Vec<String> = cell
        .state
        .fields
        .iter()
        .map(|f| hex32(f))
        .filter(|hex| hex != &hex32(&FIELD_ZERO))
        .collect();
    json!({
        "label": label,
        "cell_id": hex32(id.as_bytes()),
        "balance": cell.state.balance(),
        "nonce": cell.state.nonce(),
        "non_zero_fields": fields,
        "state_commitment": hex32(&cell.state_commitment()),
    })
}

fn bb_vec(values: &[BabyBear]) -> Vec<u32> {
    values.iter().map(|b| b.as_u32()).collect()
}

fn main() {
    // ------------------------------------------------------------------
    // 1. Build a tiny ledger: agent (sender) + recipient.
    // ------------------------------------------------------------------
    let mut ledger = Ledger::new();
    let agent_cell = make_cell(1, 1_000);
    let recipient_cell = make_cell(2, 500);
    let agent_id = agent_cell.id();
    let recipient_id = recipient_cell.id();

    // Grant agent a capability to recipient (open permissions, but the
    // executor still requires a capability handle).
    let mut agent_with_cap = agent_cell;
    agent_with_cap
        .capabilities
        .grant(recipient_id, AuthRequired::None);

    ledger.insert_cell(agent_with_cap).expect("insert agent");
    ledger.insert_cell(recipient_cell).expect("insert recipient");

    // Snapshot pre-state for the JSON dump.
    let pre_agent = cell_state_view("agent_pre", &ledger, &agent_id);
    let pre_recipient = cell_state_view("recipient_pre", &ledger, &recipient_id);

    // ------------------------------------------------------------------
    // 2. Build the Turn: single Transfer from agent -> recipient.
    // ------------------------------------------------------------------
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let transfer_amount: u64 = 100;
    let fee: u64 = 50;

    let mut builder = TurnBuilder::new(agent_id, 0);
    {
        let action = builder.action(agent_id, "transfer");
        action.transfer(agent_id, recipient_id, transfer_amount);
        // ParentsOwn keeps the action's authority within the agent.
        action.delegation(DelegationMode::ParentsOwn);
    }
    let turn = builder.fee(fee).build();

    let turn_hash_pre = turn.hash();

    // ------------------------------------------------------------------
    // 3. Execute, capture receipt.
    // ------------------------------------------------------------------
    let result = executor.execute(&turn, &mut ledger);
    let (_delta, receipt, computrons_used) = match result {
        TurnResult::Committed {
            ledger_delta,
            receipt,
            computrons_used,
        } => (ledger_delta, receipt, computrons_used),
        TurnResult::Rejected { reason, at_action } => {
            eprintln!("turn rejected at {:?}: {}", at_action, reason);
            std::process::exit(1);
        }
        TurnResult::Expired => {
            eprintln!("turn expired");
            std::process::exit(1);
        }
        TurnResult::Pending => {
            eprintln!("turn pending");
            std::process::exit(1);
        }
    };

    // Post-state snapshots.
    let post_agent = cell_state_view("agent_post", &ledger, &agent_id);
    let post_recipient = cell_state_view("recipient_post", &ledger, &recipient_id);

    // ------------------------------------------------------------------
    // 4. Project this Turn's effects into the Effect VM's per-cell stream
    //    (agent side, since the agent is debited).
    // ------------------------------------------------------------------
    let vm_effects = project_turn_effects_for_cell(&turn, &agent_id);

    // Effect VM expects at least one effect.
    assert!(
        !vm_effects.is_empty(),
        "no VM-side effects projected for agent {:?}",
        agent_id
    );

    // Render vm_effects for JSON.
    let vm_effects_json: Vec<Value> = vm_effects
        .iter()
        .map(|e| match e {
            effect_vm::Effect::Transfer { amount, direction } => json!({
                "type": "Transfer",
                "amount": amount,
                "direction": direction,
                "direction_meaning": if *direction == 0 { "incoming" } else { "outgoing" },
            }),
            other => json!({ "type": format!("{:?}", other) }),
        })
        .collect();

    // ------------------------------------------------------------------
    // 5. Generate trace + STARK proof using the initial agent state.
    //    Note: this is what a sovereign cell would prove; for hosted cells,
    //    the executor doesn't actually generate this proof (it walks the
    //    classical path). We're showing the *pathway*.
    // ------------------------------------------------------------------
    // initial_state seen by the AIR is the agent's PRE-execution state.
    let initial_state = effect_vm::CellState::new(1_000, 0);

    let (trace, public_inputs) = generate_effect_vm_trace(&initial_state, &vm_effects);
    let trace_height = trace.len();
    let trace_width = if trace_height > 0 { trace[0].len() } else { 0 };

    use pyana_circuit::stark::StarkAir;
    let air = EffectVmAir::new(trace_height);
    let air_name = air.air_name();
    let proof = stark::prove(&air, &trace, &public_inputs);
    let verify_result = stark::verify(&air, &proof, &public_inputs);
    let (verified, verify_error) = match &verify_result {
        Ok(()) => (true, None),
        Err(e) => (false, Some(e.clone())),
    };

    // Trim the trace's first row for the JSON dump (full trace is large).
    let trace_first_row: Vec<u32> = if trace_height > 0 {
        bb_vec(&trace[0])
    } else {
        Vec::new()
    };

    // Approximate proof size: serialize via serde_json (the wire format the
    // explorer will see). For a "real" byte count, postcard would be tighter
    // but this is what'll cross the wire to the browser.
    let proof_size_bytes = serde_json::to_vec(&proof)
        .map(|v| v.len())
        .unwrap_or(0);

    // ------------------------------------------------------------------
    // 6. Render the JSON document.
    // ------------------------------------------------------------------
    let doc = json!({
        "schema_version": 1,
        "schema_name": "pyana-observability-turn-trace-v1",
        "description": "Single-transfer turn execution + Effect VM STARK proof pathway.",
        "turn": {
            "agent": hex32(agent_id.as_bytes()),
            "nonce": turn.nonce,
            "fee": turn.fee,
            "memo": turn.memo,
            "valid_until": turn.valid_until,
            "action_count": turn.action_count(),
            "effects": render_effects(&turn),
            "turn_hash": hex32(&turn_hash_pre),
        },
        "pre_state": [pre_agent, pre_recipient],
        "post_state": [post_agent, post_recipient],
        "receipt": {
            "turn_hash": hex32(&receipt.turn_hash),
            "forest_hash": hex32(&receipt.forest_hash),
            "pre_state_hash": hex32(&receipt.pre_state_hash),
            "post_state_hash": hex32(&receipt.post_state_hash),
            "effects_hash": hex32(&receipt.effects_hash),
            "timestamp": receipt.timestamp,
            "action_count": receipt.action_count,
            "computrons_used": computrons_used,
            "agent": hex32(receipt.agent.as_bytes()),
            "federation_id": hex32(&receipt.federation_id),
            "previous_receipt_hash": receipt.previous_receipt_hash.as_ref().map(hex32),
            "finality": format!("{:?}", receipt.finality),
            "receipt_hash": hex32(&receipt.receipt_hash()),
        },
        "vm_effects": vm_effects_json,
        "air": {
            "air_name": air_name,
            "trace_width": trace_width,
            "trace_height": trace_height,
            "trace_first_row": trace_first_row,
            "public_input_count": public_inputs.len(),
            "public_inputs": bb_vec(&public_inputs),
        },
        "proof": {
            "air_name": proof.air_name,
            "trace_len": proof.trace_len,
            "num_cols": proof.num_cols,
            "fri_layers": proof.fri_commitments.len(),
            "query_count": proof.query_proofs.len(),
            "pow_bits": proof.pow_bits,
            "size_bytes_json": proof_size_bytes,
            "trace_commitment": hex32(&proof.trace_commitment),
            "constraint_commitment": hex32(&proof.constraint_commitment),
        },
        "verification": {
            "verified": verified,
            "error": verify_error,
            "trace_len": proof.trace_len,
            "public_input_count": public_inputs.len(),
        },
        "notes": {
            "scope": "Demo: hosted-cell turn whose Effect VM proof would be required if the agent cell were sovereign. The executor itself did NOT generate this proof — it took the classical path. We generate the proof out-of-band to demonstrate the pathway.",
            "projection_source": "Duplicated from pyana_turn::executor::TurnExecutor::convert_turn_effects_to_vm (private). See README for follow-up.",
        }
    });

    let serialized = serde_json::to_string_pretty(&doc).expect("serialize");
    println!("{}", serialized);
}


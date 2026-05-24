//! wasm-bindgen bindings for PyanaRuntime.
//!
//! All public functions here are `#[wasm_bindgen]` and take/return JsValue or primitives.
//! Complex types are serialized via serde-wasm-bindgen.

use serde::{Deserialize, Serialize};
use wasm_bindgen::prelude::*;

use pyana_cell::{AuthRequired, CellId};
use pyana_intent::{ActionPattern, Constraint, IntentKind};
use pyana_turn::conditional::ProofCondition;
use pyana_turn::{Effect, TurnResult};

use crate::runtime::{PyanaRuntime, TraceStep};

// ============================================================================
// Global runtime store (WASM is single-threaded, so this is safe)
// ============================================================================

use std::cell::RefCell;

thread_local! {
    static RUNTIMES: RefCell<Vec<Option<PyanaRuntime>>> = const { RefCell::new(Vec::new()) };
}

fn with_runtime<F, R>(handle: usize, f: F) -> Result<R, JsError>
where
    F: FnOnce(&mut PyanaRuntime) -> Result<R, String>,
{
    RUNTIMES.with(|runtimes| {
        let mut runtimes = runtimes.borrow_mut();
        let rt = runtimes
            .get_mut(handle)
            .and_then(|slot| slot.as_mut())
            .ok_or_else(|| JsError::new("invalid runtime handle"))?;
        f(rt).map_err(|e| JsError::new(&e))
    })
}

fn with_runtime_ref<F, R>(handle: usize, f: F) -> Result<R, JsError>
where
    F: FnOnce(&PyanaRuntime) -> Result<R, String>,
{
    RUNTIMES.with(|runtimes| {
        let runtimes = runtimes.borrow();
        let rt = runtimes
            .get(handle)
            .and_then(|slot| slot.as_ref())
            .ok_or_else(|| JsError::new("invalid runtime handle"))?;
        f(rt).map_err(|e| JsError::new(&e))
    })
}

// ============================================================================
// World Management
// ============================================================================

/// Create a new PyanaRuntime and return its handle.
#[wasm_bindgen]
pub fn create_runtime() -> usize {
    RUNTIMES.with(|runtimes| {
        let mut runtimes = runtimes.borrow_mut();
        // Reuse a tombstone slot if available.
        for (i, slot) in runtimes.iter_mut().enumerate() {
            if slot.is_none() {
                *slot = Some(PyanaRuntime::new());
                return i;
            }
        }
        let handle = runtimes.len();
        runtimes.push(Some(PyanaRuntime::new()));
        handle
    })
}

/// Destroy a runtime, freeing its resources. Returns true if the handle was valid.
#[wasm_bindgen]
pub fn destroy_runtime(handle: usize) -> bool {
    RUNTIMES.with(|runtimes| {
        let mut runtimes = runtimes.borrow_mut();
        match runtimes.get_mut(handle) {
            Some(slot @ Some(_)) => {
                *slot = None;
                true
            }
            _ => false,
        }
    })
}

/// Create a cell directly in the runtime's ledger.
///
/// `owner_pk` is a 32-byte public key (hex string).
/// Returns JSON with the cell_id.
#[wasm_bindgen]
pub fn create_cell(
    handle: usize,
    owner_pk_hex: &str,
    initial_balance: u64,
) -> Result<JsValue, JsError> {
    with_runtime(handle, |rt| {
        let pk = hex_decode_32(owner_pk_hex)?;
        let token_id = *blake3::hash(b"pyana-wasm-default-domain").as_bytes();
        let cell = pyana_cell::Cell::with_balance(pk, token_id, initial_balance);
        let cell_id = cell.id();
        rt.ledger.insert_cell(cell).map_err(|e| format!("{e}"))?;

        #[derive(Serialize)]
        struct CreateCellResult {
            cell_id: String,
        }
        let result = CreateCellResult {
            cell_id: hex_encode(&cell_id.0),
        };
        serde_wasm_bindgen::to_value(&result).map_err(|e| e.to_string())
    })
}

/// Get the state of a cell.
#[wasm_bindgen]
pub fn get_cell_state(handle: usize, cell_id_hex: &str) -> Result<JsValue, JsError> {
    with_runtime_ref(handle, |rt| {
        let cell_id = parse_cell_id(cell_id_hex)?;
        let cell = rt
            .ledger
            .get(&cell_id)
            .ok_or_else(|| format!("cell not found: {cell_id_hex}"))?;

        #[derive(Serialize)]
        struct CellStateView {
            cell_id: String,
            public_key: String,
            balance: u64,
            nonce: u64,
            fields: Vec<String>,
            num_capabilities: usize,
            permissions: PermissionsView,
            proved_state: bool,
            delegation_epoch: u64,
        }

        #[derive(Serialize)]
        struct PermissionsView {
            send: String,
            receive: String,
            set_state: String,
            set_permissions: String,
            delegate: String,
            access: String,
        }

        let result = CellStateView {
            cell_id: hex_encode(&cell.id().0),
            public_key: hex_encode(cell.public_key()),
            balance: cell.state.balance(),
            nonce: cell.state.nonce(),
            fields: cell.state.fields.iter().map(|f| hex_encode(f)).collect(),
            num_capabilities: cell.capabilities.len(),
            permissions: PermissionsView {
                send: format!("{:?}", cell.permissions.send),
                receive: format!("{:?}", cell.permissions.receive),
                set_state: format!("{:?}", cell.permissions.set_state),
                set_permissions: format!("{:?}", cell.permissions.set_permissions),
                delegate: format!("{:?}", cell.permissions.delegate),
                access: format!("{:?}", cell.permissions.access),
            },
            proved_state: cell.state.proved_state(),
            delegation_epoch: cell.state.delegation_epoch(),
        };
        serde_wasm_bindgen::to_value(&result).map_err(|e| e.to_string())
    })
}

/// Get all cells in the ledger.
#[wasm_bindgen]
pub fn get_all_cells(handle: usize) -> Result<JsValue, JsError> {
    with_runtime_ref(handle, |rt| {
        #[derive(Serialize)]
        struct CellSummary {
            cell_id: String,
            balance: u64,
            nonce: u64,
            num_capabilities: usize,
        }

        let cells: Vec<CellSummary> = rt
            .ledger
            .iter()
            .map(|(id, cell)| CellSummary {
                cell_id: hex_encode(&id.0),
                balance: cell.state.balance(),
                nonce: cell.state.nonce(),
                num_capabilities: cell.capabilities.len(),
            })
            .collect();

        serde_wasm_bindgen::to_value(&cells).map_err(|e| e.to_string())
    })
}

// ============================================================================
// Agent / Wallet
// ============================================================================

/// Create an agent (wallet + cell) in the runtime.
/// Returns the agent index (handle).
#[wasm_bindgen]
pub fn create_agent(handle: usize, name: &str, initial_balance: u64) -> Result<JsValue, JsError> {
    with_runtime(handle, |rt| {
        let idx = rt.create_agent(name, initial_balance);
        let agent = &rt.agents[idx];

        #[derive(Serialize)]
        struct AgentResult {
            agent_index: usize,
            name: String,
            cell_id: String,
            public_key: String,
        }

        let result = AgentResult {
            agent_index: idx,
            name: agent.name.clone(),
            cell_id: hex_encode(&agent.cell_id.0),
            public_key: hex_encode(&agent.public_key),
        };
        serde_wasm_bindgen::to_value(&result).map_err(|e| e.to_string())
    })
}

/// Mint a token for an agent (for intent matching).
/// `actions_json` is a JSON array of strings like `["read", "write"]`.
#[wasm_bindgen]
pub fn agent_mint_token(
    handle: usize,
    agent_index: usize,
    resource: &str,
    actions_json: &str,
    expiry: u64,
) -> Result<JsValue, JsError> {
    with_runtime(handle, |rt| {
        if agent_index >= rt.agents.len() {
            return Err("invalid agent index".to_string());
        }
        let actions: Vec<String> = serde_json::from_str(actions_json).map_err(|e| e.to_string())?;
        let exp = if expiry == 0 { None } else { Some(expiry) };
        let token_idx = rt.agent_mint_token(agent_index, resource, &actions, exp);

        #[derive(Serialize)]
        struct MintResult {
            token_index: usize,
            token_id: String,
        }

        let result = MintResult {
            token_index: token_idx,
            token_id: rt.agents[agent_index].held_tokens[token_idx]
                .token_id
                .clone(),
        };
        serde_wasm_bindgen::to_value(&result).map_err(|e| e.to_string())
    })
}

/// Attenuate an existing held token by narrowing its actions/resource.
#[wasm_bindgen]
pub fn agent_attenuate(
    handle: usize,
    agent_index: usize,
    token_index: usize,
    restrict_actions_json: &str,
    restrict_resource: &str,
) -> Result<JsValue, JsError> {
    with_runtime(handle, |rt| {
        if agent_index >= rt.agents.len() {
            return Err("invalid agent index".to_string());
        }
        let agent = &mut rt.agents[agent_index];
        if token_index >= agent.held_tokens.len() {
            return Err("invalid token index".to_string());
        }

        let restrict_actions: Vec<String> =
            serde_json::from_str(restrict_actions_json).map_err(|e| e.to_string())?;

        // Clone and attenuate.
        let source = &agent.held_tokens[token_index];
        agent.token_counter += 1;
        let new_id = format!("tok_{}_{}_att", agent.name, agent.token_counter);

        let mut attenuated = source.clone();
        attenuated.token_id = new_id.clone();
        if !restrict_actions.is_empty() {
            attenuated
                .actions
                .retain(|a| restrict_actions.contains(a) || a == "*");
            if attenuated.actions.contains(&"*".to_string()) && !restrict_actions.is_empty() {
                attenuated.actions = restrict_actions;
            }
        }
        if !restrict_resource.is_empty() {
            attenuated.resource = restrict_resource.to_string();
        }

        let new_idx = agent.held_tokens.len();
        agent.held_tokens.push(attenuated);

        #[derive(Serialize)]
        struct AttenuateResult {
            new_token_index: usize,
            token_id: String,
        }
        let result = AttenuateResult {
            new_token_index: new_idx,
            token_id: new_id,
        };
        serde_wasm_bindgen::to_value(&result).map_err(|e| e.to_string())
    })
}

// ============================================================================
// Turn Execution
// ============================================================================

/// Build and execute a turn for an agent.
///
/// `actions_json` is a JSON array of action descriptors:
/// ```json
/// [
///   { "type": "transfer", "to": "<cell_id_hex>", "amount": 100 },
///   { "type": "set_field", "cell": "<cell_id_hex>", "index": 0, "value_hex": "..." },
///   { "type": "increment_nonce", "cell": "<cell_id_hex>" }
/// ]
/// ```
#[wasm_bindgen]
pub fn execute_turn(
    handle: usize,
    agent_index: usize,
    actions_json: &str,
    fee: u64,
) -> Result<JsValue, JsError> {
    with_runtime(handle, |rt| {
        if agent_index >= rt.agents.len() {
            return Err("invalid agent index".to_string());
        }

        let raw_actions: Vec<RawAction> =
            serde_json::from_str(actions_json).map_err(|e| e.to_string())?;

        let agent_cell_id = rt.agents[agent_index].cell_id;
        let effects = parse_effects(&raw_actions, &agent_cell_id)?;

        let result = rt.execute_turn_for_agent(agent_index, effects, fee);
        serialize_turn_result(&result)
    })
}

/// Execute a turn step-by-step and return the execution trace.
/// Same input format as `execute_turn` but returns detailed trace info.
#[wasm_bindgen]
pub fn execute_turn_step_by_step(
    handle: usize,
    agent_index: usize,
    actions_json: &str,
    fee: u64,
) -> Result<JsValue, JsError> {
    with_runtime(handle, |rt| {
        if agent_index >= rt.agents.len() {
            return Err("invalid agent index".to_string());
        }

        let raw_actions: Vec<RawAction> =
            serde_json::from_str(actions_json).map_err(|e| e.to_string())?;

        let agent_cell_id = rt.agents[agent_index].cell_id;
        let effects = parse_effects(&raw_actions, &agent_cell_id)?;

        // Collect trace steps by examining effects.
        let mut trace_steps: Vec<TraceStep> = Vec::new();
        for (i, effect) in effects.iter().enumerate() {
            trace_steps.push(TraceStep {
                action_path: vec![0, i],
                target_cell: hex_encode(&agent_cell_id.0),
                method: "execute".to_string(),
                effects: vec![format!("{:?}", effect)],
                result: "pending".to_string(),
                computrons_used: 0,
            });
        }

        let result = rt.execute_turn_for_agent(agent_index, effects, fee);

        // Update trace with result.
        match &result {
            TurnResult::Committed {
                computrons_used, ..
            } => {
                for step in &mut trace_steps {
                    step.result = "committed".to_string();
                    step.computrons_used = *computrons_used;
                }
            }
            TurnResult::Rejected { reason, at_action } => {
                for step in &mut trace_steps {
                    step.result = format!("rejected: {reason} at {:?}", at_action);
                }
            }
            _ => {}
        }

        #[derive(Serialize)]
        struct TraceResult {
            steps: Vec<TraceStep>,
            final_result: serde_json::Value,
        }

        let final_result = match &result {
            TurnResult::Committed {
                receipt,
                computrons_used,
                ..
            } => serde_json::json!({
                "status": "committed",
                "computrons_used": computrons_used,
                "turn_hash": hex_encode(&receipt.turn_hash),
                "post_state_hash": hex_encode(&receipt.post_state_hash),
            }),
            TurnResult::Rejected { reason, at_action } => serde_json::json!({
                "status": "rejected",
                "reason": format!("{reason}"),
                "at_action": at_action,
            }),
            TurnResult::Expired => serde_json::json!({ "status": "expired" }),
            TurnResult::Pending => serde_json::json!({ "status": "pending" }),
        };

        let trace = TraceResult {
            steps: trace_steps,
            final_result,
        };
        serde_wasm_bindgen::to_value(&trace).map_err(|e| e.to_string())
    })
}

// ============================================================================
// Capabilities
// ============================================================================

/// Grant a capability from one agent to another.
#[wasm_bindgen]
pub fn grant_capability(
    handle: usize,
    from_agent: usize,
    to_agent: usize,
    target_cell_hex: &str,
    permission: &str,
) -> Result<JsValue, JsError> {
    with_runtime(handle, |rt| {
        if from_agent >= rt.agents.len() || to_agent >= rt.agents.len() {
            return Err("invalid agent index".to_string());
        }

        let perm = parse_auth_required(permission)?;
        let target_cell_id = if target_cell_hex.is_empty() {
            rt.agents[from_agent].cell_id
        } else {
            parse_cell_id(target_cell_hex)?
        };

        // Grant capability on to_agent's cell pointing to target_cell_id.
        let to_cell_id = rt.agents[to_agent].cell_id;
        let to_cell = rt
            .ledger
            .get_mut(&to_cell_id)
            .ok_or_else(|| "to_agent cell not found".to_string())?;
        let slot = to_cell
            .capabilities
            .grant(target_cell_id, perm)
            .ok_or_else(|| "capability slot overflow".to_string())?;

        #[derive(Serialize)]
        struct GrantResult {
            slot: u32,
            target_cell: String,
            to_agent_cell: String,
        }
        let result = GrantResult {
            slot,
            target_cell: hex_encode(&target_cell_id.0),
            to_agent_cell: hex_encode(&to_cell_id.0),
        };
        serde_wasm_bindgen::to_value(&result).map_err(|e| e.to_string())
    })
}

/// Revoke a capability by slot.
#[wasm_bindgen]
pub fn revoke_capability(handle: usize, agent_index: usize, slot: u32) -> Result<JsValue, JsError> {
    with_runtime(handle, |rt| {
        if agent_index >= rt.agents.len() {
            return Err("invalid agent index".to_string());
        }
        let cell_id = rt.agents[agent_index].cell_id;
        let cell = rt
            .ledger
            .get_mut(&cell_id)
            .ok_or_else(|| "cell not found".to_string())?;
        let revoked = cell.capabilities.revoke(slot);

        #[derive(Serialize)]
        struct RevokeResult {
            revoked: bool,
            slot: u32,
        }
        let result = RevokeResult { revoked, slot };
        serde_wasm_bindgen::to_value(&result).map_err(|e| e.to_string())
    })
}

/// Get the capability tree (CDT) for an agent's cell.
#[wasm_bindgen]
pub fn get_capability_tree(handle: usize, agent_index: usize) -> Result<JsValue, JsError> {
    with_runtime_ref(handle, |rt| {
        if agent_index >= rt.agents.len() {
            return Err("invalid agent index".to_string());
        }
        let cell_id = rt.agents[agent_index].cell_id;
        let cell = rt
            .ledger
            .get(&cell_id)
            .ok_or_else(|| "cell not found".to_string())?;

        #[derive(Serialize)]
        struct CapEntry {
            slot: u32,
            target: String,
            permissions: String,
            has_breadstuff: bool,
        }

        let entries: Vec<CapEntry> = cell
            .capabilities
            .iter()
            .map(|cap| CapEntry {
                slot: cap.slot,
                target: hex_encode(&cap.target.0),
                permissions: format!("{:?}", cap.permissions),
                has_breadstuff: cap.breadstuff.is_some(),
            })
            .collect();

        #[derive(Serialize)]
        struct CDTView {
            cell_id: String,
            agent_name: String,
            capabilities: Vec<CapEntry>,
        }

        let result = CDTView {
            cell_id: hex_encode(&cell_id.0),
            agent_name: rt.agents[agent_index].name.clone(),
            capabilities: entries,
        };
        serde_wasm_bindgen::to_value(&result).map_err(|e| e.to_string())
    })
}

// ============================================================================
// Notes & Bridge
// ============================================================================

/// Create a note commitment for an agent.
#[wasm_bindgen]
pub fn create_note(
    handle: usize,
    agent_index: usize,
    value: u64,
    asset_type: u64,
) -> Result<JsValue, JsError> {
    with_runtime(handle, |rt| {
        if agent_index >= rt.agents.len() {
            return Err("invalid agent index".to_string());
        }
        let commitment = rt.create_note(agent_index, value, asset_type);

        #[derive(Serialize)]
        struct NoteResult {
            commitment: String,
            value: u64,
            asset_type: u64,
        }
        let result = NoteResult {
            commitment: hex_encode(&commitment.0),
            value,
            asset_type,
        };
        serde_wasm_bindgen::to_value(&result).map_err(|e| e.to_string())
    })
}

/// Spend a note (reveal its nullifier).
#[wasm_bindgen]
pub fn spend_note(
    handle: usize,
    agent_index: usize,
    value: u64,
    asset_type: u64,
) -> Result<JsValue, JsError> {
    with_runtime(handle, |rt| {
        if agent_index >= rt.agents.len() {
            return Err("invalid agent index".to_string());
        }
        let nullifier = rt.spend_note(agent_index, value, asset_type)?;

        #[derive(Serialize)]
        struct SpendResult {
            nullifier: String,
            spent: bool,
        }
        let result = SpendResult {
            nullifier: hex_encode(&nullifier.0),
            spent: true,
        };
        serde_wasm_bindgen::to_value(&result).map_err(|e| e.to_string())
    })
}

// ============================================================================
// Federation
// ============================================================================

/// Create a simulated federation.
#[wasm_bindgen]
pub fn create_federation(handle: usize, name: &str, num_nodes: usize) -> Result<JsValue, JsError> {
    with_runtime(handle, |rt| {
        let idx = rt.create_federation(name, num_nodes);
        let fed = &rt.federations[idx];

        #[derive(Serialize)]
        struct FedResult {
            fed_index: usize,
            name: String,
            num_nodes: usize,
        }
        let result = FedResult {
            fed_index: idx,
            name: fed.name.clone(),
            num_nodes: fed.nodes.len(),
        };
        serde_wasm_bindgen::to_value(&result).map_err(|e| e.to_string())
    })
}

/// Propose a block of events to a federation.
#[wasm_bindgen]
pub fn propose_block(
    handle: usize,
    fed_index: usize,
    events_json: &str,
) -> Result<JsValue, JsError> {
    with_runtime(handle, |rt| {
        if fed_index >= rt.federations.len() {
            return Err("invalid federation index".to_string());
        }
        let events: Vec<String> = serde_json::from_str(events_json).map_err(|e| e.to_string())?;
        let event_data: Vec<Vec<u8>> = events.iter().map(|e| e.as_bytes().to_vec()).collect();
        let block_hash = rt.propose_block(fed_index, event_data);

        #[derive(Serialize)]
        struct BlockResult {
            block_hash: String,
            height: u64,
        }
        let result = BlockResult {
            block_hash: hex_encode(&block_hash),
            height: rt.federations[fed_index].height,
        };
        serde_wasm_bindgen::to_value(&result).map_err(|e| e.to_string())
    })
}

/// Get federation state.
#[wasm_bindgen]
pub fn get_federation_state(handle: usize, fed_index: usize) -> Result<JsValue, JsError> {
    with_runtime_ref(handle, |rt| {
        if fed_index >= rt.federations.len() {
            return Err("invalid federation index".to_string());
        }
        let fed = &rt.federations[fed_index];

        #[derive(Serialize)]
        struct FedState {
            name: String,
            height: u64,
            num_nodes: usize,
            num_events: usize,
            num_finalized_roots: usize,
            latest_root: Option<String>,
        }
        let result = FedState {
            name: fed.name.clone(),
            height: fed.height,
            num_nodes: fed.nodes.len(),
            num_events: fed.events.len(),
            num_finalized_roots: fed.finalized_roots.len(),
            latest_root: fed.finalized_roots.last().map(|r| hex_encode(r)),
        };
        serde_wasm_bindgen::to_value(&result).map_err(|e| e.to_string())
    })
}

/// Simulate a consensus round.
#[wasm_bindgen]
pub fn simulate_consensus_round(handle: usize, fed_index: usize) -> Result<JsValue, JsError> {
    with_runtime(handle, |rt| {
        if fed_index >= rt.federations.len() {
            return Err("invalid federation index".to_string());
        }
        let result = rt.simulate_consensus_round(fed_index);
        serde_wasm_bindgen::to_value(&result).map_err(|e| e.to_string())
    })
}

// ============================================================================
// Intents
// ============================================================================

/// Create an intent.
///
/// `kind`: "Need", "Offer", or "Query"
/// `actions_json`: `[{"action": "read", "resource": "docs/*"}, ...]`
/// `constraints_json`: `[{"AppId": "x"}, {"Service": "y"}, ...]`
#[wasm_bindgen]
pub fn create_intent(
    handle: usize,
    agent_index: usize,
    kind: &str,
    actions_json: &str,
    constraints_json: &str,
    resource_pattern: &str,
    expiry: u64,
) -> Result<JsValue, JsError> {
    with_runtime(handle, |rt| {
        if agent_index >= rt.agents.len() {
            return Err("invalid agent index".to_string());
        }
        let intent_kind = match kind {
            "Need" | "need" => IntentKind::Need,
            "Offer" | "offer" => IntentKind::Offer,
            "Query" | "query" => IntentKind::Query,
            _ => return Err(format!("unknown intent kind: {kind}")),
        };

        let actions: Vec<RawActionPattern> =
            serde_json::from_str(actions_json).map_err(|e| e.to_string())?;
        let action_patterns: Vec<ActionPattern> = actions
            .into_iter()
            .map(|a| ActionPattern {
                action: a.action,
                resource: a.resource,
            })
            .collect();

        let raw_constraints: Vec<RawConstraint> =
            serde_json::from_str(constraints_json).map_err(|e| e.to_string())?;
        let constraints: Vec<Constraint> = raw_constraints
            .into_iter()
            .filter_map(|c| parse_constraint(c))
            .collect();

        let res_pattern = if resource_pattern.is_empty() {
            None
        } else {
            Some(resource_pattern.to_string())
        };

        let id = rt.create_intent(
            agent_index,
            intent_kind,
            action_patterns,
            constraints,
            res_pattern,
            expiry,
        );

        #[derive(Serialize)]
        struct IntentResult {
            intent_id: String,
            intent_index: usize,
        }
        let result = IntentResult {
            intent_id: hex_encode(&id),
            intent_index: rt.intents.len() - 1,
        };
        serde_wasm_bindgen::to_value(&result).map_err(|e| e.to_string())
    })
}

/// Match an intent against an agent's held tokens.
#[wasm_bindgen]
pub fn match_intent_for_agent(
    handle: usize,
    intent_index: usize,
    agent_index: usize,
) -> Result<JsValue, JsError> {
    with_runtime_ref(handle, |rt| {
        if intent_index >= rt.intents.len() {
            return Err("invalid intent index".to_string());
        }
        if agent_index >= rt.agents.len() {
            return Err("invalid agent index".to_string());
        }
        let result = rt.match_intent_for_agent(intent_index, agent_index);

        #[derive(Serialize)]
        struct MatchResultView {
            matched: bool,
            kind: String,
            token_index: Option<usize>,
            token_indices: Option<Vec<usize>>,
        }

        let view = match result {
            pyana_intent::matcher::MatchResult::Matched { token_index, .. } => MatchResultView {
                matched: true,
                kind: "matched".to_string(),
                token_index: Some(token_index),
                token_indices: None,
            },
            pyana_intent::matcher::MatchResult::CompoundMatched { token_indices, .. } => {
                MatchResultView {
                    matched: true,
                    kind: "compound_matched".to_string(),
                    token_index: None,
                    token_indices: Some(token_indices),
                }
            }
            pyana_intent::matcher::MatchResult::NoMatch => MatchResultView {
                matched: false,
                kind: "no_match".to_string(),
                token_index: None,
                token_indices: None,
            },
            pyana_intent::matcher::MatchResult::Expired => MatchResultView {
                matched: false,
                kind: "expired".to_string(),
                token_index: None,
                token_indices: None,
            },
            pyana_intent::matcher::MatchResult::WrongKind => MatchResultView {
                matched: false,
                kind: "wrong_kind".to_string(),
                token_index: None,
                token_indices: None,
            },
        };
        serde_wasm_bindgen::to_value(&view).map_err(|e| e.to_string())
    })
}

// ============================================================================
// Conditional Turns
// ============================================================================

/// Submit a conditional turn (executes only when condition is proven).
#[wasm_bindgen]
pub fn submit_conditional(
    handle: usize,
    agent_index: usize,
    actions_json: &str,
    fee: u64,
    condition_json: &str,
    timeout_blocks: u64,
) -> Result<JsValue, JsError> {
    with_runtime(handle, |rt| {
        if agent_index >= rt.agents.len() {
            return Err("invalid agent index".to_string());
        }

        let raw_actions: Vec<RawAction> =
            serde_json::from_str(actions_json).map_err(|e| e.to_string())?;
        let agent_cell_id = rt.agents[agent_index].cell_id;
        let effects = parse_effects(&raw_actions, &agent_cell_id)?;

        let raw_condition: RawCondition =
            serde_json::from_str(condition_json).map_err(|e| e.to_string())?;
        let condition = parse_condition(raw_condition)?;

        let id = rt.submit_conditional(agent_index, effects, fee, condition, timeout_blocks);

        #[derive(Serialize)]
        struct ConditionalResult {
            conditional_id: String,
            timeout_height: u64,
        }
        let result = ConditionalResult {
            conditional_id: hex_encode(&id),
            timeout_height: rt.current_height + timeout_blocks,
        };
        serde_wasm_bindgen::to_value(&result).map_err(|e| e.to_string())
    })
}

/// Advance the block height for timeout simulation.
#[wasm_bindgen]
pub fn advance_height(handle: usize, blocks: u64) -> Result<JsValue, JsError> {
    with_runtime(handle, |rt| {
        rt.advance_height(blocks);

        #[derive(Serialize)]
        struct HeightResult {
            height: u64,
            timestamp: i64,
        }
        let result = HeightResult {
            height: rt.current_height,
            timestamp: rt.current_timestamp,
        };
        serde_wasm_bindgen::to_value(&result).map_err(|e| e.to_string())
    })
}

// ============================================================================
// Revocation Channels
// ============================================================================

/// Create a revocation channel for an agent.
#[wasm_bindgen]
pub fn create_revocation_channel(handle: usize, revoker_agent: usize) -> Result<JsValue, JsError> {
    with_runtime(handle, |rt| {
        if revoker_agent >= rt.agents.len() {
            return Err("invalid agent index".to_string());
        }
        let channel_id = rt.create_revocation_channel(revoker_agent);

        #[derive(Serialize)]
        struct ChannelResult {
            channel_id: String,
        }
        let result = ChannelResult {
            channel_id: hex_encode(&channel_id),
        };
        serde_wasm_bindgen::to_value(&result).map_err(|e| e.to_string())
    })
}

/// Trip a revocation channel.
#[wasm_bindgen]
pub fn trip_revocation_channel(
    handle: usize,
    revoker_agent: usize,
    channel_id_hex: &str,
) -> Result<JsValue, JsError> {
    with_runtime(handle, |rt| {
        if revoker_agent >= rt.agents.len() {
            return Err("invalid agent index".to_string());
        }
        let channel_id = hex_decode_32(channel_id_hex)?;
        let reason = *blake3::hash(b"revoked-via-playground").as_bytes();
        let tripped = rt.trip_channel(&channel_id, revoker_agent, reason);

        #[derive(Serialize)]
        struct TripResult {
            tripped: bool,
            channel_id: String,
        }
        let result = TripResult {
            tripped,
            channel_id: hex_encode(&channel_id),
        };
        serde_wasm_bindgen::to_value(&result).map_err(|e| e.to_string())
    })
}

/// Check if a revocation channel is active.
#[wasm_bindgen]
pub fn is_channel_active(handle: usize, channel_id_hex: &str) -> Result<JsValue, JsError> {
    with_runtime_ref(handle, |rt| {
        let channel_id = hex_decode_32(channel_id_hex)?;
        let active = rt.is_channel_active(&channel_id);

        #[derive(Serialize)]
        struct ActiveResult {
            channel_id: String,
            active: bool,
        }
        let result = ActiveResult {
            channel_id: hex_encode(&channel_id),
            active,
        };
        serde_wasm_bindgen::to_value(&result).map_err(|e| e.to_string())
    })
}

// ============================================================================
// Visualization Helpers
// ============================================================================

/// Get the Merkle tree visualization data (for SVG rendering).
#[wasm_bindgen]
pub fn get_merkle_tree_viz(handle: usize) -> Result<JsValue, JsError> {
    with_runtime(handle, |rt| {
        let root = rt.ledger.root();
        let num_cells = rt.ledger.len();

        #[derive(Serialize)]
        struct TreeViz {
            root_hex: String,
            num_leaves: usize,
            tree_type: String,
        }
        let result = TreeViz {
            root_hex: hex_encode(&root),
            num_leaves: num_cells,
            tree_type: "binary_blake3".to_string(),
        };
        serde_wasm_bindgen::to_value(&result).map_err(|e| e.to_string())
    })
}

/// Get the receipt chain for the runtime.
#[wasm_bindgen]
pub fn get_receipt_chain(handle: usize) -> Result<JsValue, JsError> {
    with_runtime_ref(handle, |rt| {
        #[derive(Serialize)]
        struct ReceiptView {
            turn_hash: String,
            pre_state_hash: String,
            post_state_hash: String,
            timestamp: i64,
            computrons_used: u64,
            action_count: usize,
        }

        let chain: Vec<ReceiptView> = rt
            .receipts
            .iter()
            .map(|r| ReceiptView {
                turn_hash: hex_encode(&r.turn_hash),
                pre_state_hash: hex_encode(&r.pre_state_hash),
                post_state_hash: hex_encode(&r.post_state_hash),
                timestamp: r.timestamp,
                computrons_used: r.computrons_used,
                action_count: r.action_count,
            })
            .collect();

        serde_wasm_bindgen::to_value(&chain).map_err(|e| e.to_string())
    })
}

/// Get the delegation graph (all capabilities across all cells).
#[wasm_bindgen]
pub fn get_delegation_graph(handle: usize) -> Result<JsValue, JsError> {
    with_runtime_ref(handle, |rt| {
        #[derive(Serialize)]
        struct GraphNode {
            cell_id: String,
            agent_name: Option<String>,
        }

        #[derive(Serialize)]
        struct GraphEdge {
            from: String,
            to: String,
            slot: u32,
            permissions: String,
        }

        #[derive(Serialize)]
        struct DelegationGraph {
            nodes: Vec<GraphNode>,
            edges: Vec<GraphEdge>,
        }

        let mut nodes = Vec::new();
        let mut edges = Vec::new();

        for (cell_id, cell) in rt.ledger.iter() {
            let agent_name = rt
                .agents
                .iter()
                .find(|a| a.cell_id == *cell_id)
                .map(|a| a.name.clone());

            nodes.push(GraphNode {
                cell_id: hex_encode(&cell_id.0),
                agent_name,
            });

            for cap in cell.capabilities.iter() {
                edges.push(GraphEdge {
                    from: hex_encode(&cell_id.0),
                    to: hex_encode(&cap.target.0),
                    slot: cap.slot,
                    permissions: format!("{:?}", cap.permissions),
                });
            }
        }

        let graph = DelegationGraph { nodes, edges };
        serde_wasm_bindgen::to_value(&graph).map_err(|e| e.to_string())
    })
}

// ============================================================================
// Internal helpers
// ============================================================================

fn hex_encode(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn hex_decode_32(hex: &str) -> Result<[u8; 32], String> {
    if hex.len() != 64 {
        return Err(format!(
            "expected 64 hex chars for 32 bytes, got {}",
            hex.len()
        ));
    }
    let mut result = [0u8; 32];
    for i in 0..32 {
        result[i] = u8::from_str_radix(&hex[i * 2..i * 2 + 2], 16)
            .map_err(|e| format!("invalid hex at byte {i}: {e}"))?;
    }
    Ok(result)
}

fn parse_cell_id(hex: &str) -> Result<CellId, String> {
    let bytes = hex_decode_32(hex)?;
    Ok(CellId::from_bytes(bytes))
}

fn parse_auth_required(s: &str) -> Result<AuthRequired, String> {
    match s {
        "None" | "none" => Ok(AuthRequired::None),
        "Signature" | "signature" => Ok(AuthRequired::Signature),
        "Proof" | "proof" => Ok(AuthRequired::Proof),
        "Either" | "either" => Ok(AuthRequired::Either),
        "Impossible" | "impossible" => Ok(AuthRequired::Impossible),
        _ => Err(format!("unknown permission: {s}")),
    }
}

// --- JSON input types ---

#[derive(Deserialize)]
struct RawAction {
    #[serde(rename = "type")]
    action_type: String,
    to: Option<String>,
    from: Option<String>,
    cell: Option<String>,
    amount: Option<u64>,
    index: Option<usize>,
    value_hex: Option<String>,
}

#[derive(Deserialize)]
struct RawActionPattern {
    action: Option<String>,
    resource: Option<String>,
}

#[derive(Deserialize)]
struct RawConstraint {
    #[serde(rename = "AppId")]
    app_id: Option<String>,
    #[serde(rename = "Service")]
    service: Option<String>,
    #[serde(rename = "UserId")]
    user_id: Option<String>,
    #[serde(rename = "NotExpiredAt")]
    not_expired_at: Option<i64>,
    #[serde(rename = "Feature")]
    feature: Option<String>,
}

#[derive(Deserialize)]
struct RawCondition {
    #[serde(rename = "type")]
    condition_type: String,
    hash: Option<String>,
    federation_root: Option<String>,
    turn_hash: Option<String>,
}

fn parse_constraint(raw: RawConstraint) -> Option<Constraint> {
    if let Some(v) = raw.app_id {
        return Some(Constraint::AppId(v));
    }
    if let Some(v) = raw.service {
        return Some(Constraint::Service(v));
    }
    if let Some(v) = raw.user_id {
        return Some(Constraint::UserId(v));
    }
    if let Some(v) = raw.not_expired_at {
        return Some(Constraint::NotExpiredAt(v));
    }
    if let Some(v) = raw.feature {
        return Some(Constraint::Feature(v));
    }
    None
}

fn parse_condition(raw: RawCondition) -> Result<ProofCondition, String> {
    match raw.condition_type.as_str() {
        "hash_preimage" => {
            let hash_hex = raw.hash.ok_or("hash_preimage requires 'hash' field")?;
            let hash = hex_decode_32(&hash_hex)?;
            Ok(ProofCondition::HashPreimage { hash })
        }
        "turn_executed" => {
            let hash_hex = raw
                .turn_hash
                .ok_or("turn_executed requires 'turn_hash' field")?;
            let turn_hash = hex_decode_32(&hash_hex)?;
            Ok(ProofCondition::TurnExecuted { turn_hash })
        }
        "remote_proof" => {
            let root_hex = raw
                .federation_root
                .ok_or("remote_proof requires 'federation_root' field")?;
            let federation_root = hex_decode_32(&root_hex)?;
            Ok(ProofCondition::RemoteProof {
                federation_root,
                expected_air: "merkle_membership".to_string(),
                expected_conclusion: 1,
            })
        }
        other => Err(format!("unknown condition type: {other}")),
    }
}

fn parse_effects(raw_actions: &[RawAction], agent_cell_id: &CellId) -> Result<Vec<Effect>, String> {
    let mut effects = Vec::new();
    for action in raw_actions {
        match action.action_type.as_str() {
            "transfer" => {
                let to_hex = action.to.as_ref().ok_or("transfer requires 'to' field")?;
                let to = parse_cell_id(to_hex)?;
                let amount = action.amount.ok_or("transfer requires 'amount' field")?;
                let from = if let Some(ref from_hex) = action.from {
                    parse_cell_id(from_hex)?
                } else {
                    *agent_cell_id
                };
                effects.push(Effect::Transfer { from, to, amount });
            }
            "set_field" => {
                let cell = if let Some(ref cell_hex) = action.cell {
                    parse_cell_id(cell_hex)?
                } else {
                    *agent_cell_id
                };
                let index = action.index.ok_or("set_field requires 'index' field")?;
                let value_hex = action
                    .value_hex
                    .as_ref()
                    .ok_or("set_field requires 'value_hex' field")?;
                let value = hex_decode_32(value_hex)?;
                effects.push(Effect::SetField { cell, index, value });
            }
            "increment_nonce" => {
                let cell = if let Some(ref cell_hex) = action.cell {
                    parse_cell_id(cell_hex)?
                } else {
                    *agent_cell_id
                };
                effects.push(Effect::IncrementNonce { cell });
            }
            other => {
                return Err(format!("unknown action type: {other}"));
            }
        }
    }
    Ok(effects)
}

fn serialize_turn_result(result: &TurnResult) -> Result<JsValue, String> {
    #[derive(Serialize)]
    struct TurnResultView {
        status: String,
        turn_hash: Option<String>,
        computrons_used: Option<u64>,
        pre_state_hash: Option<String>,
        post_state_hash: Option<String>,
        error: Option<String>,
        at_action: Option<Vec<usize>>,
    }

    let view = match result {
        TurnResult::Committed {
            receipt,
            computrons_used,
            ..
        } => TurnResultView {
            status: "committed".to_string(),
            turn_hash: Some(hex_encode(&receipt.turn_hash)),
            computrons_used: Some(*computrons_used),
            pre_state_hash: Some(hex_encode(&receipt.pre_state_hash)),
            post_state_hash: Some(hex_encode(&receipt.post_state_hash)),
            error: None,
            at_action: None,
        },
        TurnResult::Rejected { reason, at_action } => TurnResultView {
            status: "rejected".to_string(),
            turn_hash: None,
            computrons_used: None,
            pre_state_hash: None,
            post_state_hash: None,
            error: Some(format!("{reason}")),
            at_action: Some(at_action.clone()),
        },
        TurnResult::Expired => TurnResultView {
            status: "expired".to_string(),
            turn_hash: None,
            computrons_used: None,
            pre_state_hash: None,
            post_state_hash: None,
            error: None,
            at_action: None,
        },
        TurnResult::Pending => TurnResultView {
            status: "pending".to_string(),
            turn_hash: None,
            computrons_used: None,
            pre_state_hash: None,
            post_state_hash: None,
            error: None,
            at_action: None,
        },
    };
    serde_wasm_bindgen::to_value(&view).map_err(|e| e.to_string())
}

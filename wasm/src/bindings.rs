//! wasm-bindgen bindings for DreggRuntime.
//!
//! All public functions here are `#[wasm_bindgen]` and take/return JsValue or primitives.
//! Complex types are serialized via serde-wasm-bindgen.

use serde::{Deserialize, Serialize};
use wasm_bindgen::prelude::*;

use dregg_cell::predicate::{InputRef, WitnessedPredicateKind};
use dregg_cell::program::{
    AuthorizedSet, CellProgram, HashKind, StateConstraint, TransitionCase, TransitionGuard,
};
use dregg_cell::{AuthRequired, CellId};
use dregg_intent::{ActionPattern, Constraint, IntentKind};
use dregg_turn::action::Authorization;
use dregg_turn::conditional::ProofCondition;
use dregg_turn::{Effect, TurnResult};

use crate::runtime::{DreggRuntime, TraceStep};

// ============================================================================
// Global runtime store (WASM is single-threaded, so this is safe)
// ============================================================================

use std::cell::RefCell;

thread_local! {
    static RUNTIMES: RefCell<Vec<Option<DreggRuntime>>> = const { RefCell::new(Vec::new()) };
}

fn with_runtime<F, R>(handle: usize, f: F) -> Result<R, JsError>
where
    F: FnOnce(&mut DreggRuntime) -> Result<R, String>,
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
    F: FnOnce(&DreggRuntime) -> Result<R, String>,
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

/// Create a new DreggRuntime and return its handle.
#[wasm_bindgen]
pub fn create_runtime() -> usize {
    RUNTIMES.with(|runtimes| {
        let mut runtimes = runtimes.borrow_mut();
        // Reuse a tombstone slot if available.
        for (i, slot) in runtimes.iter_mut().enumerate() {
            if slot.is_none() {
                *slot = Some(DreggRuntime::new());
                return i;
            }
        }
        let handle = runtimes.len();
        runtimes.push(Some(DreggRuntime::new()));
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

/// Create a cell in the runtime via a real `Effect::CreateCell` turn issued
/// by the genesis agent (agent 0). Requires at least one agent to exist as
/// the signer — if there are none, returns an error.
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
        let cell_id = rt.mint_cell_from_genesis(pk, initial_balance)?;

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
///
/// Refactor 6: adds `program: CellProgramView` surfacing the full slot-caveat
/// tree so JS inspectors can render a complete picture of the cell's program
/// semantics. Existing fields are byte-equivalent to the prior shape.
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
            /// Canonical `Cell::state_commitment()` — what `PeerExchange`
            /// signs over. Exposed so the JS layer can drive the peer-exchange
            /// flow without recomputing.
            state_commitment: String,
            /// Refactor 6: full cell program structure for `<dregg-cell-program>`
            /// inspector rendering.
            program: CellProgramView,
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
            state_commitment: hex_encode(&cell.state_commitment()),
            program: cell_program_to_view(&cell.program),
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
// Agent / Cipherclerk
// ============================================================================

/// Create an agent (cipherclerk + cell) in the runtime.
/// Returns the agent index (handle).
///
/// Genesis (agent 0) is birth-by-fiat: the ledger inserts the root cell
/// directly because no signer exists yet. Subsequent agents are minted
/// via `Effect::CreateCellFromFactory` against the runtime's default
/// test-cipherclerk factory — the canonical constructor-transparency path.
/// To mint from a specific factory, use
/// [`create_agent_with_factory`] / [`deploy_factory_descriptor`].
#[wasm_bindgen]
pub fn create_agent(handle: usize, name: &str, initial_balance: u64) -> Result<JsValue, JsError> {
    with_runtime(handle, |rt| {
        let idx = rt.try_create_agent(name, initial_balance)?;
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

/// Create an agent whose cell is minted from a specific factory VK
/// (instead of the runtime's default test-cipherclerk factory).
///
/// The factory must have been deployed via
/// [`deploy_factory_descriptor`]. The new cell carries a `Provenance`
/// record pointing at this factory, so a downstream `verify_provenance`
/// against the named factory set will return true.
///
/// Genesis (the first agent in the runtime) cannot be born from a
/// factory — no signer exists yet. This binding always returns an error
/// for agent index 0; create the genesis agent via [`create_agent`]
/// first, then mint subsequent agents from your factory.
#[wasm_bindgen]
pub fn create_agent_with_factory(
    handle: usize,
    name: &str,
    initial_balance: u64,
    factory_vk_hex: &str,
) -> Result<JsValue, JsError> {
    with_runtime(handle, |rt| {
        let factory_vk = hex_decode_32(factory_vk_hex)?;
        let idx = rt.try_create_agent_with_factory(name, initial_balance, &factory_vk)?;
        let agent = &rt.agents[idx];

        #[derive(Serialize)]
        struct AgentResult {
            agent_index: usize,
            name: String,
            cell_id: String,
            public_key: String,
            factory_vk: String,
        }

        let result = AgentResult {
            agent_index: idx,
            name: agent.name.clone(),
            cell_id: hex_encode(&agent.cell_id.0),
            public_key: hex_encode(&agent.public_key),
            factory_vk: hex_encode(&factory_vk),
        };
        serde_wasm_bindgen::to_value(&result).map_err(|e| e.to_string())
    })
}

/// Deploy a factory descriptor into the runtime, returning the
/// `factory_vk` that addresses it. The factory_vk can then be passed to
/// [`create_agent_with_factory`] (or to JS-side `createFromFactory`)
/// to mint cells from this factory.
///
/// `descriptor_json` is a serde-serialized `FactoryDescriptor`. Apps
/// that ship their own factories can call this at boot to register them
/// alongside the runtime's default test-cipherclerk factory.
#[wasm_bindgen]
pub fn deploy_factory_descriptor(handle: usize, descriptor_json: &str) -> Result<JsValue, JsError> {
    use dregg_cell::factory::FactoryDescriptor;

    with_runtime(handle, |rt| {
        let descriptor: FactoryDescriptor =
            serde_json::from_str(descriptor_json).map_err(|e| e.to_string())?;
        let factory_vk = rt.deploy_factory(descriptor);

        #[derive(Serialize)]
        struct DeployResult {
            factory_vk: String,
        }
        let result = DeployResult {
            factory_vk: hex_encode(&factory_vk),
        };
        serde_wasm_bindgen::to_value(&result).map_err(|e| e.to_string())
    })
}

/// Return the VK of the runtime's default test-cipherclerk factory — the
/// factory used by `create_agent` / `create_cell` when no explicit
/// factory is named.
///
/// Exposed so the JS layer can pre-register the wasm-runtime factory
/// set with `verifyProvenance` (or display the wasm-runtime's
/// constructor-transparency anchor in the inspector UI).
#[wasm_bindgen]
pub fn default_factory_vk(handle: usize) -> Result<JsValue, JsError> {
    with_runtime_ref(handle, |rt| {
        #[derive(Serialize)]
        struct VkResult {
            factory_vk: String,
        }
        let result = VkResult {
            factory_vk: hex_encode(&rt.default_factory_vk()),
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
// Agent-scoped cipherclerk getters (STARBRIDGE-PLAN §4.5 <dregg-cipherclerk> #36)
//
// Surface the real `AgentCipherclerk` state — macaroon-backed `HeldToken`s, the
// receipt chain filtered to the agent, and the stealth PUBLIC keys — replacing
// the "awaiting wasm32 support" / "TODO" placeholders in the cipherclerk
// inspector. No private key material is ever surfaced (stealth getter returns
// view+spend PUBKEYS only; spend/view private keys stay inside the cipherclerk).
// ============================================================================

/// List the macaroon-backed `HeldToken`s held by an agent's cipherclerk
/// (`AgentCipherclerk::tokens()`). Distinct from the intent-matcher
/// `HeldCapability` list surfaced by `get_capability_tree`.
///
/// Returns a JSON array of token summaries. No `root_key` / `issuer_key` is
/// surfaced (those are `#[serde(skip)]` and zeroed on drop in the SDK); only the
/// public-facing macaroon fields plus the capability flags (`can_mint`,
/// `can_prove`, `verified`) are exposed.
#[wasm_bindgen]
pub fn get_agent_tokens(handle: usize, agent_index: usize) -> Result<JsValue, JsError> {
    with_runtime_ref(handle, |rt| {
        if agent_index >= rt.agents.len() {
            return Err("invalid agent index".to_string());
        }
        let cclerk = &rt.agents[agent_index].cclerk;

        #[derive(Serialize)]
        struct HeldTokenView {
            id: String,
            label: String,
            service: String,
            encoded: String,
            verified: bool,
            can_mint: bool,
            can_prove: bool,
            caveat_chain_hash: Option<String>,
        }

        let tokens: Vec<HeldTokenView> = cclerk
            .tokens()
            .iter()
            .map(|t| HeldTokenView {
                id: t.id().to_string(),
                label: t.label().to_string(),
                service: t.service().to_string(),
                encoded: t.encoded().to_string(),
                verified: t.is_verified(),
                can_mint: t.can_mint(),
                can_prove: t.can_prove(),
                caveat_chain_hash: t.caveat_chain_hash().map(|h| hex_encode(&h)),
            })
            .collect();

        serde_wasm_bindgen::to_value(&tokens).map_err(|e| e.to_string())
    })
}

/// Get the receipt chain filtered to a single agent.
///
/// The wasm sim runtime applies turns through one shared `TurnExecutor` and
/// records receipts in `DreggRuntime::receipts` (the cipherclerk's own
/// `receipt_chain()` is not threaded in the sim path). Each `TurnReceipt`
/// carries its `agent: CellId`, so we filter the global chain by the agent's
/// cell id — the honest per-agent view. Same `ReceiptView` shape as
/// `get_receipt_chain`, minus the per-action/proof expansion (the inspector
/// drills into individual receipts via `<dregg-receipt uri="...">`).
#[wasm_bindgen]
pub fn get_agent_receipts(handle: usize, agent_index: usize) -> Result<JsValue, JsError> {
    with_runtime_ref(handle, |rt| {
        if agent_index >= rt.agents.len() {
            return Err("invalid agent index".to_string());
        }
        let cell_id = rt.agents[agent_index].cell_id;

        #[derive(Serialize)]
        struct AgentReceiptView {
            turn_hash: String,
            pre_state_hash: String,
            post_state_hash: String,
            effects_hash: String,
            timestamp: i64,
            computrons_used: u64,
            action_count: usize,
            previous_receipt_hash: Option<String>,
        }

        let chain: Vec<AgentReceiptView> = rt
            .receipts
            .iter()
            .filter(|r| r.agent == cell_id)
            .map(|r| AgentReceiptView {
                turn_hash: hex_encode(&r.turn_hash),
                pre_state_hash: hex_encode(&r.pre_state_hash),
                post_state_hash: hex_encode(&r.post_state_hash),
                effects_hash: hex_encode(&r.effects_hash),
                timestamp: r.timestamp,
                computrons_used: r.computrons_used,
                action_count: r.action_count,
                previous_receipt_hash: r.previous_receipt_hash.map(|h| hex_encode(&h)),
            })
            .collect();

        serde_wasm_bindgen::to_value(&chain).map_err(|e| e.to_string())
    })
}

/// Get an agent's stealth meta-address — the view and spend PUBLIC keys only.
///
/// Sourced from `AgentCipherclerk::stealth_meta_address()`
/// (`StealthMetaAddress { spend_pubkey, view_pubkey }`). The corresponding
/// PRIVATE keys (`view_private_key` / `spend_private_key`) are NEVER surfaced —
/// they stay inside the cipherclerk's `StealthKeys`. Publishing the meta-address
/// is the intended use: senders derive unlinkable one-time addresses from it.
#[wasm_bindgen]
pub fn get_agent_stealth_keys(handle: usize, agent_index: usize) -> Result<JsValue, JsError> {
    with_runtime_ref(handle, |rt| {
        if agent_index >= rt.agents.len() {
            return Err("invalid agent index".to_string());
        }
        let meta = rt.agents[agent_index].cclerk.stealth_meta_address();

        #[derive(Serialize)]
        struct StealthKeysView {
            spend_pubkey: String,
            view_pubkey: String,
        }

        let result = StealthKeysView {
            spend_pubkey: hex_encode(&meta.spend_pubkey),
            view_pubkey: hex_encode(&meta.view_pubkey),
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

/// List notes for an agent. Returns array of
/// `{commitment, value, asset_type, spent, nullifier}`.
///
/// Reads the agent's real `held_notes` index (#45): every note minted via
/// `create_note` is recorded there (and marked spent — with its revealed
/// nullifier — once `spend_note` runs). `commitment` / `value` / `asset_type`
/// are derived from the canonical `dregg_cell::Note`, so the `<dregg-note>`
/// inspector and `dregg://note/<commitment>` URI lookups resolve real data
/// rather than the prior always-empty stub. `nullifier` is `null` until spent.
#[wasm_bindgen]
pub fn get_notes(handle: usize, agent_index: usize) -> Result<JsValue, JsError> {
    with_runtime_ref(handle, |rt| {
        if agent_index >= rt.agents.len() {
            return Err("invalid agent index".to_string());
        }
        #[derive(Serialize)]
        struct NoteItem {
            commitment: String,
            value: u64,
            asset_type: u64,
            spent: bool,
            nullifier: Option<String>,
        }
        let notes: Vec<NoteItem> = rt.agents[agent_index]
            .held_notes
            .iter()
            .map(|hn| NoteItem {
                commitment: hex_encode(&hn.note.commitment().0),
                value: hn.note.value(),
                asset_type: hn.note.asset_type(),
                spent: hn.nullifier.is_some(),
                nullifier: hn.nullifier.map(|n| hex_encode(&n.0)),
            })
            .collect();
        serde_wasm_bindgen::to_value(&notes).map_err(|e| e.to_string())
    })
}

// ============================================================================
// Federation
// ============================================================================

// Federation bindings: surface the real `dregg_federation::Federation` to
// the Studio. All hashes / signatures / merkle roots returned to JS come
// from the canonical crate's types; no JS-side simulation lives in
// runtime-in-memory.js for these paths.

/// Create a federation with `num_nodes` real federation nodes. Each node has
/// a freshly generated Ed25519 keypair and an empty `RevocationTree`. The
/// federation index is its handle for subsequent calls.
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
            threshold: usize,
            max_faults: usize,
        }
        let threshold = fed.federation.threshold() as usize;
        // max_faults = n - threshold (BFT tolerance)
        let max_faults = fed.node_count.saturating_sub(threshold);
        let result = FedResult {
            fed_index: idx,
            name: fed.name.clone(),
            num_nodes: fed.node_count,
            threshold,
            max_faults,
        };
        serde_wasm_bindgen::to_value(&result).map_err(|e| e.to_string())
    })
}

/// List the KnownFederations registry (wasm/sim surface for §5.7).
/// Returns the SimFederations the runtime knows (analog to node
/// KnownFederations for the federation-list inspector).
#[wasm_bindgen]
pub fn list_known_federations(handle: usize) -> Result<JsValue, JsError> {
    with_runtime_ref(handle, |rt| {
        #[derive(Serialize)]
        struct KnownFed {
            index: usize,
            name: String,
            federation_id: String,
            threshold: usize,
            num_nodes: usize,
            /// Block height (monotonic in SimFederation); useful for Starbridge
            /// federation-list + block-dag inspectors to show progress without extra calls.
            height: u64,
        }
        let list: Vec<KnownFed> = rt
            .federations
            .iter()
            .enumerate()
            .map(|(i, sf)| {
                let c = &sf.federation;
                KnownFed {
                    index: i,
                    name: sf.name.clone(),
                    federation_id: hex_encode(&c.id().0),
                    threshold: c.threshold() as usize,
                    num_nodes: sf.node_count,
                    height: sf.height,
                }
            })
            .collect();
        Ok(serde_wasm_bindgen::to_value(&list).map_err(|e| e.to_string())?)
    })
}

/// Register (or record) a federation in the runtime's known set (sim).
/// committee_pubkeys_json: array of hex pubkeys (minimal: derives n).
/// Unblocks extension `registerFederation` + list in plan §4.3/§5.7.
#[wasm_bindgen]
pub fn register_federation(
    handle: usize,
    name: &str,
    committee_pubkeys_json: &str,
) -> Result<JsValue, JsError> {
    with_runtime(handle, |rt| {
        let keys: Vec<String> = serde_json::from_str(committee_pubkeys_json)
            .map_err(|e| format!("bad pubkeys json: {e}"))?;
        let n = keys.len().max(1);
        let idx = rt.create_federation(name, n);
        #[derive(Serialize)]
        struct RegResult {
            registered_index: usize,
            name: String,
        }
        Ok(serde_wasm_bindgen::to_value(&RegResult {
            registered_index: idx,
            name: name.to_string(),
        })
        .map_err(|e| e.to_string())?)
    })
}

/// Submit a batch of revocation events from node 0 and immediately drive
/// a consensus round. `events_json` is a JSON array of token-id strings;
/// each becomes a `RevocationEvent` signed by node 0's signing key.
///
/// Behavioral note vs. the deleted SimFederation: real `run_consensus_round`
/// requires the leader's `pending_events` to be non-empty AND a quorum of
/// online nodes (n - floor(n/3)) to vote — proposing with no events or with
/// too few online nodes will return `block_hash: null`.
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
        let block_hash = rt.propose_block(fed_index, events);
        let height = rt.federations[fed_index].height;

        #[derive(Serialize)]
        struct BlockResult {
            block_hash: Option<String>,
            height: u64,
            finalized: bool,
        }
        let result = BlockResult {
            block_hash: block_hash.map(|h| hex_encode(&h)),
            height,
            finalized: block_hash.is_some(),
        };
        serde_wasm_bindgen::to_value(&result).map_err(|e| e.to_string())
    })
}

/// Get a snapshot of federation state — node count, finalized history depth,
/// latest attested root, etc. All values derived from the canonical
/// `Federation` committee + local consensus state.
#[wasm_bindgen]
pub fn get_federation_state(handle: usize, fed_index: usize) -> Result<JsValue, JsError> {
    with_runtime_ref(handle, |rt| {
        if fed_index >= rt.federations.len() {
            return Err("invalid federation index".to_string());
        }
        let fed = &rt.federations[fed_index];
        let canonical = &fed.federation;

        let num_finalized = fed.finalized_blocks.len();
        let latest_root = fed
            .finalized_blocks
            .last()
            .map(|b| hex_encode(&b.block_hash));

        // Total event count across all finalized blocks.
        let num_events: usize = fed
            .finalized_blocks
            .iter()
            .map(|b| b.revoked_token_ids.len())
            .sum();

        // Per-node view: the canonical `Federation` holds the committee pubkeys;
        // all nodes are always online in the wasm sim (no crash/recover API).
        #[derive(Serialize)]
        struct NodeView {
            node_id: usize,
            name: String,
            public_key: String,
            is_online: bool,
            revoked_count: usize,
        }
        let members = canonical.members();
        let total_revoked = fed.revoked_set.len();
        let nodes: Vec<NodeView> = members
            .iter()
            .enumerate()
            .map(|(i, pk)| NodeView {
                node_id: i,
                name: format!("{}-{i}", fed.name),
                public_key: hex_encode(&pk.0),
                is_online: true,
                revoked_count: total_revoked,
            })
            .collect();

        #[derive(Serialize)]
        struct FedState {
            fed_index: usize,
            name: String,
            height: u64,
            num_nodes: usize,
            online_nodes: usize,
            threshold: usize,
            epoch: u64,
            num_events: usize,
            num_finalized_roots: usize,
            latest_root: Option<String>,
            nodes: Vec<NodeView>,
        }
        let result = FedState {
            fed_index,
            name: fed.name.clone(),
            height: fed.height,
            num_nodes: fed.node_count,
            online_nodes: fed.node_count,
            threshold: canonical.threshold() as usize,
            epoch: canonical.epoch(),
            num_events,
            num_finalized_roots: num_finalized,
            latest_root,
            nodes,
        };
        serde_wasm_bindgen::to_value(&result).map_err(|e| e.to_string())
    })
}

/// Drive a single consensus round on the federation without submitting new
/// events (events already in `pending_events` will be picked up). Returns
/// the finalized block summary or null if the round did not finalize.
#[wasm_bindgen]
pub fn simulate_consensus_round(handle: usize, fed_index: usize) -> Result<JsValue, JsError> {
    with_runtime(handle, |rt| {
        if fed_index >= rt.federations.len() {
            return Err("invalid federation index".to_string());
        }
        let outcome = rt.simulate_consensus_round(fed_index);
        serde_wasm_bindgen::to_value(&outcome).map_err(|e| e.to_string())
    })
}

/// Get a finalized block by height (1-indexed; height 1 = first finalized
/// block). Returns `null` if the height has not been finalized.
#[wasm_bindgen]
pub fn get_federation_block(
    handle: usize,
    fed_index: usize,
    height: u64,
) -> Result<JsValue, JsError> {
    with_runtime_ref(handle, |rt| {
        if fed_index >= rt.federations.len() {
            return Err("invalid federation index".to_string());
        }
        let fed = &rt.federations[fed_index];
        if height == 0 {
            return serde_wasm_bindgen::to_value(&serde_json::Value::Null)
                .map_err(|e| e.to_string());
        }
        let block = fed.finalized_blocks.iter().find(|b| b.height == height);
        let block = match block {
            Some(b) => b,
            None => {
                return serde_wasm_bindgen::to_value(&serde_json::Value::Null)
                    .map_err(|e| e.to_string());
            }
        };

        #[derive(Serialize)]
        struct BlockView {
            fed_index: usize,
            height: u64,
            view: u64,
            proposer: usize,
            block_hash: String,
            prev_hash: String,
            pre_state_root: String,
            post_state_root: String,
            events: Vec<String>,
            num_votes: usize,
            qc_threshold: usize,
        }
        let result = BlockView {
            fed_index,
            height: block.height,
            view: block.view,
            proposer: 0,
            block_hash: hex_encode(&block.block_hash),
            // Real predecessor hash — the height-(N-1) block's hash, folded into
            // this block's `block_hash` at finalization (see FinalizedBlock /
            // propose_block). Genesis-most block links to all-zeros. This gives
            // <dregg-block-dag> real edges.
            prev_hash: hex_encode(&block.prev_hash),
            // Real ledger Merkle root captured at block time (Ledger::root()).
            // A wasm-sim consensus round finalizes revocations only — it does
            // not apply ledger turns — so pre == post for any single block, but
            // both are the ledger's genuine root, not all-zeros. Gives
            // <dregg-block> a real state anchor.
            pre_state_root: hex_encode(&block.pre_state_root),
            post_state_root: hex_encode(&block.post_state_root),
            events: block.revoked_token_ids.clone(),
            num_votes: block.qc_votes,
            qc_threshold: block.qc_threshold,
        };
        serde_wasm_bindgen::to_value(&result).map_err(|e| e.to_string())
    })
}

/// List all finalized block headers for a federation. Each entry is a
/// compact summary; call `get_federation_block(fed_idx, height)` for the
/// full view. Returns an empty list if nothing has been finalized.
#[wasm_bindgen]
pub fn list_federation_blocks(handle: usize, fed_index: usize) -> Result<JsValue, JsError> {
    with_runtime_ref(handle, |rt| {
        if fed_index >= rt.federations.len() {
            return Err("invalid federation index".to_string());
        }
        let fed = &rt.federations[fed_index];

        #[derive(Serialize)]
        struct BlockSummary {
            fed_index: usize,
            height: u64,
            view: u64,
            block_hash: String,
            /// Real predecessor hash — lets <dregg-block-dag> draw edges from
            /// the summary list alone (no per-block get_federation_block call).
            prev_hash: String,
            num_events: usize,
        }
        let blocks: Vec<BlockSummary> = fed
            .finalized_blocks
            .iter()
            .map(|b| BlockSummary {
                fed_index,
                height: b.height,
                view: b.view,
                block_hash: hex_encode(&b.block_hash),
                prev_hash: hex_encode(&b.prev_hash),
                num_events: b.revoked_token_ids.len(),
            })
            .collect();
        serde_wasm_bindgen::to_value(&blocks).map_err(|e| e.to_string())
    })
}

/* Blocklace / peer / delegation / merkle surface (STARBRIDGE FOLLOWUP-09):
 * Existing: list_federation_blocks (1055), get_federation_block, get_delegation_graph (1840),
 * create/verify/decode_peer_transition (1451+), merkle_*_proof + get_merkle_tree_viz, list_known_federations.
 * These power the 4 inspectors + block-dag + federation views without JS reimpl (delegates to Rust
 * dregg_federation + blocklace crate used in node).
 * No new list_blocklace/simulate_peer_transition needed for current studio (sim is educational carve-out;
 * live via node MCP dregg_get_blocklace_status + constitution at node/src/mcp.rs:3841+ and blocklace/src/*).
 * Future: if exposing full dregg_blocklace::Blocklace to wasm for Remote parity, add here after reading
 * blocklace/src/lib.rs + node/blocklace_sync + with_runtime pattern. See PLAN §4.5, §5, §8.
 * (Read before this comment edit per rules; no cargo.)
 */*/

// --- Wave 3 Batch 2 supporting bindings (federation-list, factory, dfa stubs) ---

// (deduped in STARBRIDGE-FOLLOWUP-07: the Wave-3 duplicate of list_known_federations +
//  register_federation was removed; canonical is the §5.7 pubkeys version below + enriched list.
//  This resolves conflicting entrypoints in the wasm surface visible to Starbridge federation inspectors
//  and extension registerFederation calls.)

/// List every factory deployed in the runtime's executor (read path for
/// `<dregg-factory-descriptor>`).
///
/// Walks the canonical `executor.factory_registry` (`FactoryRegistry::descriptors`)
/// and surfaces each deployed `FactoryDescriptor`'s real metadata: its VK, the
/// counts of state/field constraints and allowed capability templates, default
/// cell mode, optional child program VK, and creation budget. The runtime's
/// default test-cipherclerk factory is flagged so the inspector can distinguish
/// it. This replaces the prior coarse stub that hardcoded `has_state_constraints:
/// false` and only ever returned the default VK.
#[wasm_bindgen]
pub fn list_deployed_factories(handle: usize) -> Result<JsValue, JsError> {
    with_runtime_ref(handle, |rt| {
        #[derive(Serialize)]
        struct FactorySummary {
            vk: String,
            is_default: bool,
            default_mode: String,
            num_state_constraints: usize,
            num_field_constraints: usize,
            num_allowed_cap_templates: usize,
            has_state_constraints: bool,
            child_program_vk: Option<String>,
            creation_budget: Option<u64>,
        }

        let default_vk = rt.default_factory_vk();
        let registry = rt.executor.factory_registry.borrow();
        let mut out: Vec<FactorySummary> = registry
            .descriptors
            .iter()
            .map(|(vk, d)| FactorySummary {
                vk: hex_encode(vk),
                is_default: *vk == default_vk,
                default_mode: format!("{:?}", d.default_mode),
                num_state_constraints: d.state_constraints.len(),
                num_field_constraints: d.field_constraints.len(),
                num_allowed_cap_templates: d.allowed_cap_templates.len(),
                has_state_constraints: !d.state_constraints.is_empty(),
                child_program_vk: d.child_program_vk.as_ref().map(|v| hex_encode(v)),
                creation_budget: d.creation_budget,
            })
            .collect();
        // Deterministic order for stable inspector rendering (HashMap iteration
        // order is nondeterministic); default factory first, then by VK.
        out.sort_by(|a, b| b.is_default.cmp(&a.is_default).then(a.vk.cmp(&b.vk)));
        serde_wasm_bindgen::to_value(&out).map_err(|e| e.to_string())
    })
}

/// DFA compile/eval stub. In full: delegates to dregg_dfa::compiler + air.
/// For inspector <dregg-dfa> + relay/pubsub. Returns placeholder shape today.
#[wasm_bindgen]
pub fn compile_dfa(_pattern_json: &str) -> Result<JsValue, JsError> {
    // Placeholder — real path wires dfa crate when DFA lane + wasm gate complete.
    #[derive(Serialize)]
    struct DfaStub {
        states: u32,
        transitions: u32,
        note: &'static str,
    }
    serde_wasm_bindgen::to_value(&DfaStub {
        states: 0,
        transitions: 0,
        note: "dfa wasm binding pending DFA-RATIONALIZATION + dfa feature gate",
    })
    .map_err(|e| JsError::new(&e.to_string()))
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
            dregg_intent::matcher::MatchResult::Matched { token_index, .. } => MatchResultView {
                matched: true,
                kind: "matched".to_string(),
                token_index: Some(token_index),
                token_indices: None,
            },
            dregg_intent::matcher::MatchResult::CompoundMatched { token_indices, .. } => {
                MatchResultView {
                    matched: true,
                    kind: "compound_matched".to_string(),
                    token_index: None,
                    token_indices: Some(token_indices),
                }
            }
            dregg_intent::matcher::MatchResult::NoMatch => MatchResultView {
                matched: false,
                kind: "no_match".to_string(),
                token_index: None,
                token_indices: None,
            },
            dregg_intent::matcher::MatchResult::Expired => MatchResultView {
                matched: false,
                kind: "expired".to_string(),
                token_index: None,
                token_indices: None,
            },
            dregg_intent::matcher::MatchResult::WrongKind => MatchResultView {
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

/// List pending conditional turns in the runtime (for <dregg-conditional-turn>).
/// Uses the real PendingConditional vec from runtime; condition simplified to string tag.
#[wasm_bindgen]
pub fn get_pending_conditionals(handle: usize) -> Result<JsValue, JsError> {
    with_runtime(handle, |rt| {
        #[derive(Serialize)]
        struct CondView {
            id: String,
            timeout_height: u64,
            submitted_height: u64,
            condition_kind: String,
        }
        let views: Vec<CondView> = rt
            .conditionals
            .iter()
            .map(|pc| {
                let kind = match &pc.conditional.condition {
                    ProofCondition::HashPreimage { .. } => "HashPreimage",
                    ProofCondition::TurnExecuted { .. } => "TurnExecuted",
                    ProofCondition::RemoteProof { .. } => "RemoteProof",
                    ProofCondition::LocalProof { .. } => "LocalProof",
                }
                .to_string();
                CondView {
                    id: hex_encode(&pc.id),
                    timeout_height: pc.conditional.timeout_height,
                    submitted_height: pc.submitted_height,
                    condition_kind: kind,
                }
            })
            .collect();
        serde_wasm_bindgen::to_value(&views).map_err(|e| e.to_string())
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

// ============================================================================
// Peer Exchange (sovereign-cell P2P)
//
// Direct facade over `dregg_cell::PeerExchange` (canonical sovereign-cell
// peer protocol). Each agent owns one `PeerExchange` constructed with the
// cipherclerk's real Ed25519 signing key. These bindings carry no cryptographic
// logic — they just marshal arguments into / out of the canonical type.
// ============================================================================

/// Register a peer cell on the named agent's exchange session, anchoring it
/// to an initial commitment that the two parties agreed on out-of-band.
/// Must be called before `verify_peer_transition` will accept transitions
/// from that peer.
#[wasm_bindgen]
pub fn register_peer(
    handle: usize,
    agent_idx: usize,
    peer_cell_id_hex: &str,
    peer_pubkey_hex: &str,
    initial_commitment_hex: &str,
) -> Result<JsValue, JsError> {
    with_runtime(handle, |rt| {
        let peer_cell_id = parse_cell_id(peer_cell_id_hex)?;
        let peer_pubkey = hex_decode_32(peer_pubkey_hex)?;
        let initial_commitment = hex_decode_32(initial_commitment_hex)?;
        rt.agent_register_peer(agent_idx, peer_cell_id, initial_commitment)?;

        #[derive(Serialize)]
        struct Registered {
            agent_index: usize,
            peer_cell_id: String,
            peer_pubkey: String,
            initial_commitment: String,
        }
        serde_wasm_bindgen::to_value(&Registered {
            agent_index: agent_idx,
            peer_cell_id: hex_encode(&peer_cell_id.0),
            peer_pubkey: hex_encode(&peer_pubkey),
            initial_commitment: hex_encode(&initial_commitment),
        })
        .map_err(|e| e.to_string())
    })
}

/// Sign a state-transition for the named agent's exchange session and
/// return the postcard-encoded `PeerStateTransition` bytes. Bytes — not
/// JSON — because the whole point is a compact signed blob that can be
/// base64-encoded for paste UX.
#[wasm_bindgen]
pub fn create_peer_transition(
    handle: usize,
    agent_idx: usize,
    old_commit_hex: &str,
    new_commit_hex: &str,
    effects_hash_hex: &str,
) -> Result<Vec<u8>, JsError> {
    with_runtime(handle, |rt| {
        let old_c = hex_decode_32(old_commit_hex)?;
        let new_c = hex_decode_32(new_commit_hex)?;
        let eh = hex_decode_32(effects_hash_hex)?;
        rt.agent_create_peer_transition(agent_idx, old_c, new_c, eh)
    })
}

/// Postcard-decode a peer transition's bytes and verify it against the
/// named agent's exchange session. On success returns the updated
/// `PeerCellView` shape (with hex-encoded commitment + sequence +
/// last-updated). On rejection returns a `JsError` whose message includes
/// the typed variant name (e.g. `"InvalidSignature: invalid Ed25519
/// signature"`) so the UI can switch on the code.
#[wasm_bindgen]
pub fn verify_peer_transition(
    handle: usize,
    agent_idx: usize,
    transition_bytes: &[u8],
    peer_pubkey_hex: &str,
) -> Result<JsValue, JsError> {
    let peer_pubkey = hex_decode_32(peer_pubkey_hex).map_err(|e| JsError::new(&e))?;
    RUNTIMES.with(|runtimes| {
        let mut runtimes = runtimes.borrow_mut();
        let rt = runtimes
            .get_mut(handle)
            .and_then(|slot| slot.as_mut())
            .ok_or_else(|| JsError::new("invalid runtime handle"))?;
        match rt.agent_verify_peer_transition(agent_idx, transition_bytes, peer_pubkey) {
            Ok(view) => {
                let serializable = peer_cell_view_to_serializable(&view);
                serde_wasm_bindgen::to_value(&serializable)
                    .map_err(|e| JsError::new(&e.to_string()))
            }
            Err((variant, msg)) => Err(JsError::new(&format!("{variant}: {msg}"))),
        }
    })
}

/// Read the agent's current view of a peer cell — commitment, sequence,
/// timestamp. Returns `null` if the peer has not been registered.
#[wasm_bindgen]
pub fn get_peer_view(
    handle: usize,
    agent_idx: usize,
    peer_cell_id_hex: &str,
) -> Result<JsValue, JsError> {
    with_runtime_ref(handle, |rt| {
        let peer_cell_id = parse_cell_id(peer_cell_id_hex)?;
        let view = rt.agent_get_peer_view(agent_idx, peer_cell_id)?;
        match view {
            Some(v) => serde_wasm_bindgen::to_value(&peer_cell_view_to_serializable(&v))
                .map_err(|e| e.to_string()),
            None => {
                serde_wasm_bindgen::to_value(&serde_json::Value::Null).map_err(|e| e.to_string())
            }
        }
    })
}

/// List all peer cell ids the agent has registered (hex strings).
#[wasm_bindgen]
pub fn list_peers(handle: usize, agent_idx: usize) -> Result<JsValue, JsError> {
    with_runtime_ref(handle, |rt| {
        let peers = rt.agent_list_peers(agent_idx)?;
        let hexes: Vec<String> = peers.iter().map(|c| hex_encode(&c.0)).collect();
        serde_wasm_bindgen::to_value(&hexes).map_err(|e| e.to_string())
    })
}

/// Convenience: get the agent's PeerExchange public key. Useful for the
/// paste-UX where one side needs to share the verifying key with the
/// other up-front.
#[wasm_bindgen]
pub fn get_peer_pubkey(handle: usize, agent_idx: usize) -> Result<JsValue, JsError> {
    with_runtime_ref(handle, |rt| {
        let pk = rt.agent_peer_pubkey(agent_idx)?;

        #[derive(Serialize)]
        struct PubkeyView {
            agent_index: usize,
            public_key: String,
        }
        serde_wasm_bindgen::to_value(&PubkeyView {
            agent_index: agent_idx,
            public_key: hex_encode(&pk),
        })
        .map_err(|e| e.to_string())
    })
}

/// Read the current canonical state-commitment of a cell — what the agent
/// signs over when emitting a `PeerStateTransition`. Returns `null` if the
/// cell isn't in the ledger.
#[wasm_bindgen]
pub fn get_cell_state_commitment(handle: usize, cell_id_hex: &str) -> Result<JsValue, JsError> {
    with_runtime_ref(handle, |rt| {
        let cell_id = parse_cell_id(cell_id_hex)?;
        match rt.cell_state_commitment(&cell_id) {
            Some(commit) => {
                #[derive(Serialize)]
                struct CommitView {
                    cell_id: String,
                    state_commitment: String,
                }
                serde_wasm_bindgen::to_value(&CommitView {
                    cell_id: hex_encode(&cell_id.0),
                    state_commitment: hex_encode(&commit),
                })
                .map_err(|e| e.to_string())
            }
            None => {
                serde_wasm_bindgen::to_value(&serde_json::Value::Null).map_err(|e| e.to_string())
            }
        }
    })
}

#[derive(Serialize)]
struct PeerCellViewSerializable {
    cell_id: String,
    last_known_commitment: String,
    last_sequence: u64,
    last_updated: i64,
}

fn peer_cell_view_to_serializable(view: &dregg_cell::PeerCellView) -> PeerCellViewSerializable {
    PeerCellViewSerializable {
        cell_id: hex_encode(&view.cell_id.0),
        last_known_commitment: hex_encode(&view.last_known_commitment),
        last_sequence: view.last_sequence,
        last_updated: view.last_updated,
    }
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

/// List all known revocation channels (ids + active state). Now uses real
/// RevocationChannelSet::iter() (the TODO is resolved; inspector cluster A).
/// Enables <dregg-revocation-channel> list + URI views with live state.
#[wasm_bindgen]
pub fn list_revocation_channels(handle: usize) -> Result<JsValue, JsError> {
    with_runtime_ref(handle, |rt| {
        #[derive(Serialize)]
        struct ChanView {
            channel_id: String,
            active: bool,
            revoker: String,
            created_at: u64,
        }
        let chans: Vec<ChanView> = rt
            .revocation_channels
            .iter()
            .map(|(id, ch)| ChanView {
                channel_id: hex_encode(id),
                active: ch.is_active(),
                revoker: hex_encode(ch.revoker.as_bytes()),
                created_at: ch.created_at,
            })
            .collect();
        serde_wasm_bindgen::to_value(&chans).map_err(|e| e.to_string())
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
///
/// Refactor 3: adds `actions: Vec<ActionView>` per receipt, each with
/// `target_cell`, `method`, `effects`, and `authorization` (6-variant tagged union).
/// Refactor 7: adds `proof_view: Option<ProofView>` per receipt for γ.2 bilateral
/// PI rendering by `<dregg-proof>`.
/// Existing fields are byte-equivalent to the prior shape.
#[wasm_bindgen]
pub fn get_receipt_chain(handle: usize) -> Result<JsValue, JsError> {
    with_runtime_ref(handle, |rt| {
        #[derive(Serialize)]
        struct ReceiptView {
            // --- existing fields (unchanged) ---
            turn_hash: String,
            pre_state_hash: String,
            post_state_hash: String,
            timestamp: i64,
            computrons_used: u64,
            action_count: usize,
            // --- Refactor 3: per-action authorization ---
            actions: Vec<ActionView>,
            // --- Refactor 7: per-receipt proof metadata ---
            proof_view: Option<ProofView>,
        }

        let chain: Vec<ReceiptView> = rt
            .receipts
            .iter()
            .zip(rt.turns.iter())
            .map(|(r, t)| {
                // Refactor 3: walk the call forest and project each action.
                let actions = collect_actions_from_forest(t);
                // Refactor 7: the wasm runtime does not run the Effect VM
                // STARK (no proof generation in-browser). Receipts from the
                // sim runtime are scope-0 (no attached proof). Surface None
                // with a gap-note so inspectors can show "no proof — sim
                // runtime" clearly. If a proof were attached via a
                // WitnessedReceipt wrapper, we'd decode it here.
                let proof_view: Option<ProofView> = None;

                ReceiptView {
                    turn_hash: hex_encode(&r.turn_hash),
                    pre_state_hash: hex_encode(&r.pre_state_hash),
                    post_state_hash: hex_encode(&r.post_state_hash),
                    timestamp: r.timestamp,
                    computrons_used: r.computrons_used,
                    action_count: r.action_count,
                    actions,
                    proof_view,
                }
            })
            .collect();

        serde_wasm_bindgen::to_value(&chain).map_err(|e| e.to_string())
    })
}

// ============================================================================
// Refactor 8 — decode_peer_transition
//
// Decode postcard-encoded PeerStateTransition bytes into a structured JS
// value. Today the JS layer only sees opaque bytes; this binding surfaces
// all fields: cell_id, old_commitment, new_commitment, effects_hash,
// timestamp, sequence, signature (64-byte hex), and transition_proof
// presence.
// ============================================================================

/// Postcard-decode a `PeerStateTransition` and return its fields as a
/// structured JS object. The transition_bytes are the raw postcard bytes
/// returned by `create_peer_transition`.
///
/// Returns `{ cell_id, old_commitment, new_commitment, effects_hash,
///   timestamp, sequence, signature, has_transition_proof }`.
/// Full proof bytes are NOT included by default (too large for render);
/// `has_transition_proof: bool` tells the inspector whether one is
/// attached.
#[wasm_bindgen]
pub fn decode_peer_transition(bytes: &[u8]) -> Result<JsValue, JsError> {
    use dregg_cell::PeerStateTransition;

    let transition: PeerStateTransition =
        postcard::from_bytes(bytes).map_err(|e| JsError::new(&format!("decode error: {e}")))?;

    #[derive(Serialize)]
    struct PeerTransitionView {
        cell_id: String,
        old_commitment: String,
        new_commitment: String,
        effects_hash: String,
        timestamp: i64,
        sequence: u64,
        /// 64-byte Ed25519 signature, hex-encoded.
        signature: String,
        /// True if a STARK proof is attached (full bytes not surfaced for
        /// default render — use a dedicated endpoint for the raw proof).
        has_transition_proof: bool,
    }

    let view = PeerTransitionView {
        cell_id: hex_encode(&transition.cell_id.0),
        old_commitment: hex_encode(&transition.old_commitment),
        new_commitment: hex_encode(&transition.new_commitment),
        effects_hash: hex_encode(&transition.effects_hash),
        timestamp: transition.timestamp,
        sequence: transition.sequence,
        signature: hex_encode(&transition.signature),
        has_transition_proof: transition.transition_proof.is_some(),
    };

    serde_wasm_bindgen::to_value(&view).map_err(|e| JsError::new(&e.to_string()))
}

// ============================================================================
// Refactor 5 (new) — get_turn_trace
//
// Return the execution trace for a completed turn identified by its
// turn_hash. The wasm runtime does not persist a full EffectVM trace
// (no STARK proof generation in-browser) — the trace recorded by
// `execute_turn_step_by_step` is ephemeral and not stored per-turn.
//
// What IS stored is the receipt + committed turn (call forest). This
// binding surfaces the receipt's per-action effect log as a trace-step
// list so `<dregg-trace>` can walk execution.
//
// Gap note: a full EffectVM trace (151-column AIR rows) is not available
// from the sim runtime. What we surface is:
//  - One step per action in the call forest
//  - Each step has: action_path, target_cell, method (hex symbol),
//    effects (Debug-printed), computrons_used (from receipt total)
//
// For a real node receipt with a WitnessedReceipt (scope-2) attached,
// the full trace rows would be decoded from WitnessBundle::trace_rows.
// ============================================================================

/// Return trace steps for the committed turn identified by `turn_hash_hex`.
/// If the turn is not found in the receipt chain, returns `null`.
///
/// Each step: `{ action_path: number[], target_cell: string, method: string,
///   effects: string[], computrons_used: number, result: string }`.
#[wasm_bindgen]
pub fn get_turn_trace(handle: usize, turn_hash_hex: &str) -> Result<JsValue, JsError> {
    with_runtime_ref(handle, |rt| {
        let turn_hash = hex_decode_32(turn_hash_hex)?;

        // Find the receipt (and parallel turn) by turn_hash.
        let idx = rt.receipts.iter().position(|r| r.turn_hash == turn_hash);

        let idx = match idx {
            Some(i) => i,
            None => {
                return serde_wasm_bindgen::to_value(&serde_json::Value::Null)
                    .map_err(|e| e.to_string());
            }
        };

        let receipt = &rt.receipts[idx];
        let turn = &rt.turns[idx];

        // Build per-step trace from the call forest.
        let steps = collect_trace_steps_from_forest(turn, receipt.computrons_used);

        #[derive(Serialize)]
        struct TurnTraceView {
            turn_hash: String,
            computrons_total: u64,
            steps: Vec<TraceStep>,
            /// Gap note: full EffectVM AIR trace rows are not available from
            /// the sim runtime. Steps are derived from the stored call forest.
            trace_gap_note: String,
        }

        let view = TurnTraceView {
            turn_hash: hex_encode(&receipt.turn_hash),
            computrons_total: receipt.computrons_used,
            steps,
            trace_gap_note: "sim-runtime: no STARK proof generated; steps derived from call forest. For full AIR trace, use a WitnessedReceipt scope-2 bundle from a real node.".to_string(),
        };

        serde_wasm_bindgen::to_value(&view).map_err(|e| e.to_string())
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
// Protocol surface view types (Refactors 3, 6, 7)
// ============================================================================
//
// These serde types are used by get_receipt_chain (Refactors 3+7) and
// get_cell_state (Refactor 6). They are NOT exposed as #[wasm_bindgen]
// types — they are serialized to JsValue via serde_wasm_bindgen.

// ---------------------------------------------------------------------------
// Refactor 3: per-action authorization views
// ---------------------------------------------------------------------------

/// Per-action view for receipt chain entries (Refactor 3).
#[derive(Serialize)]
pub struct ActionView {
    pub target_cell: String,
    /// Method symbol as 64-hex string (BLAKE3 of method name).
    pub method: String,
    /// Effects Debug-printed (v0 — full structured view in future refactor).
    pub effects: Vec<String>,
    /// Per-action authorization.
    pub authorization: AuthorizationView,
}

/// Tagged-union view for Authorization (6 variants + Unchecked + OneOf).
#[derive(Serialize)]
#[serde(tag = "kind")]
pub enum AuthorizationView {
    /// Ed25519 signature (r, s as hex).
    Signature { r: String, s: String },
    /// Zero-knowledge proof authorization.
    Proof {
        bound_action: String,
        bound_resource: String,
        proof_bytes_len: usize,
    },
    /// Capability token hash (breadstuff).
    Breadstuff { token_hash: String },
    /// Bearer capability proof.
    Bearer {
        target: String,
        expires_at: u64,
        delegation_kind: String,
    },
    /// No authorization (Unchecked / None).
    Unchecked,
    /// CapTP-delivered turn authorization (Stage 7 / P1.B).
    CapTpDelivered {
        introducer_pk: String,
        sender_pk: String,
        sender_signature: String,
        /// Summary of the handoff certificate (full cert not surfaced for
        /// render — too large; see the cert's signing_message fields).
        handoff_cert_summary: HandoffCertSummary,
    },
    /// App-defined authorization via a WitnessedPredicate.
    Custom {
        predicate_kind: String,
        commitment: String,
        input_ref: String,
        proof_witness_index: usize,
    },
    /// Disjunctive 1-of-N authorization.
    OneOf {
        num_candidates: usize,
        proof_index: u32,
    },
}

/// Summary fields from a HandoffCertificate for CapTpDelivered display.
#[derive(Serialize)]
pub struct HandoffCertSummary {
    pub introducer_federation: String,
    pub recipient_pk: String,
    pub nonce: String,
}

fn authorization_to_view(auth: &Authorization) -> AuthorizationView {
    match auth {
        Authorization::Signature(r, s) => AuthorizationView::Signature {
            r: hex_encode(r),
            s: hex_encode(s),
        },
        Authorization::Proof {
            bound_action,
            bound_resource,
            proof_bytes,
        } => AuthorizationView::Proof {
            bound_action: bound_action.clone(),
            bound_resource: bound_resource.clone(),
            proof_bytes_len: proof_bytes.len(),
        },
        Authorization::Breadstuff(hash) => AuthorizationView::Breadstuff {
            token_hash: hex_encode(hash),
        },
        Authorization::Bearer(proof) => AuthorizationView::Bearer {
            target: hex_encode(&proof.target.0),
            expires_at: proof.expires_at,
            delegation_kind: match &proof.delegation_proof {
                dregg_turn::action::DelegationProofData::SignedDelegation { .. } => {
                    "SignedDelegation".to_string()
                }
                dregg_turn::action::DelegationProofData::StarkDelegation { .. } => {
                    "StarkDelegation".to_string()
                }
            },
        },
        Authorization::Unchecked => AuthorizationView::Unchecked,
        Authorization::CapTpDelivered {
            handoff_cert,
            introducer_pk,
            sender_pk,
            sender_signature,
        } => AuthorizationView::CapTpDelivered {
            introducer_pk: hex_encode(introducer_pk),
            sender_pk: hex_encode(sender_pk),
            sender_signature: hex_encode(sender_signature),
            handoff_cert_summary: HandoffCertSummary {
                introducer_federation: hex_encode(&handoff_cert.introducer.0),
                recipient_pk: hex_encode(&handoff_cert.recipient_pk),
                nonce: hex_encode(&handoff_cert.nonce),
            },
        },
        Authorization::Custom { predicate } => {
            let kind_name = witnessed_predicate_kind_name(&predicate.kind);
            let input_ref_name = input_ref_name(&predicate.input_ref);
            AuthorizationView::Custom {
                predicate_kind: kind_name,
                commitment: hex_encode(&predicate.commitment),
                input_ref: input_ref_name,
                proof_witness_index: predicate.proof_witness_index,
            }
        }
        Authorization::OneOf {
            candidates,
            proof_index,
        } => AuthorizationView::OneOf {
            num_candidates: candidates.len(),
            proof_index: *proof_index,
        },
    }
}

fn witnessed_predicate_kind_name(kind: &WitnessedPredicateKind) -> String {
    match kind {
        WitnessedPredicateKind::Dfa => "Dfa".to_string(),
        WitnessedPredicateKind::Temporal => "Temporal".to_string(),
        WitnessedPredicateKind::MerkleMembership => "MerkleMembership".to_string(),
        WitnessedPredicateKind::NonMembership => "NonMembership".to_string(),
        WitnessedPredicateKind::BlindedSet => "BlindedSet".to_string(),
        WitnessedPredicateKind::BridgePredicate => "BridgePredicate".to_string(),
        WitnessedPredicateKind::PedersenEquality => "PedersenEquality".to_string(),
        WitnessedPredicateKind::Custom { vk_hash } => {
            format!("Custom({})", &hex_encode(vk_hash)[..8])
        }
    }
}

fn input_ref_name(ir: &InputRef) -> String {
    match ir {
        InputRef::Slot { index } => format!("Slot({index})"),
        InputRef::Witness { index } => format!("Witness({index})"),
        InputRef::PublicInput { pi_index } => format!("PublicInput({pi_index})"),
        InputRef::Sender => "Sender".to_string(),
        InputRef::SigningMessage => "SigningMessage".to_string(),
    }
}

/// Walk a turn's call forest and collect ActionView for each action.
fn collect_actions_from_forest(turn: &dregg_turn::Turn) -> Vec<ActionView> {
    let mut out = Vec::new();
    for tree in &turn.call_forest.roots {
        collect_actions_from_tree(tree, &mut out);
    }
    out
}

fn collect_actions_from_tree(tree: &dregg_turn::forest::CallTree, out: &mut Vec<ActionView>) {
    let action = &tree.action;
    let effects: Vec<String> = action.effects.iter().map(|e| format!("{e:?}")).collect();
    out.push(ActionView {
        target_cell: hex_encode(&action.target.0),
        method: hex_encode(&action.method),
        effects,
        authorization: authorization_to_view(&action.authorization),
    });
    for child in &tree.children {
        collect_actions_from_tree(child, out);
    }
}

/// Walk a turn's call forest and build TraceStep entries.
fn collect_trace_steps_from_forest(
    turn: &dregg_turn::Turn,
    total_computrons: u64,
) -> Vec<TraceStep> {
    let mut out = Vec::new();
    for (root_idx, tree) in turn.call_forest.roots.iter().enumerate() {
        collect_trace_steps_from_tree(tree, &[root_idx], total_computrons, &mut out);
    }
    out
}

fn collect_trace_steps_from_tree(
    tree: &dregg_turn::forest::CallTree,
    path: &[usize],
    total_computrons: u64,
    out: &mut Vec<TraceStep>,
) {
    let action = &tree.action;
    let effects: Vec<String> = action.effects.iter().map(|e| format!("{e:?}")).collect();
    out.push(TraceStep {
        action_path: path.to_vec(),
        target_cell: hex_encode(&action.target.0),
        method: hex_encode(&action.method),
        effects,
        result: "committed".to_string(),
        computrons_used: total_computrons,
    });
    for (child_idx, child) in tree.children.iter().enumerate() {
        let mut child_path = path.to_vec();
        child_path.push(child_idx);
        collect_trace_steps_from_tree(child, &child_path, total_computrons, out);
    }
}

// ---------------------------------------------------------------------------
// Refactor 7: per-receipt proof metadata view
// ---------------------------------------------------------------------------

/// Proof metadata view for a receipt (Refactor 7).
///
/// The wasm sim runtime does not generate STARK proofs — receipts are
/// scope-0. When a WitnessedReceipt (scope-1/2) is available, ProofView
/// would be populated with kind, public_inputs, and bilateral PI fields.
#[derive(Serialize)]
pub struct ProofView {
    /// Proof system identifier (e.g. "stark-effect-vm", "plonky3-recursion").
    pub kind: String,
    /// Public inputs as hex strings (4-felt chunks encoded as 32 bytes each).
    pub public_inputs: Vec<String>,
    /// γ.2 bilateral PI (None when not a cross-cell receipt).
    pub bilateral_pi: Option<BilateralPiView>,
    /// True when this receipt's PI includes the IS_AGENT_CELL flag.
    pub is_agent_cell: bool,
    /// True when this receipt's PI includes the IS_SOVEREIGN_CELL flag.
    pub is_sovereign_cell: bool,
}

/// γ.2 bilateral binding public inputs (Stage 7-γ.2).
/// Surfaces outgoing/incoming Merkle accumulator roots for Transfer,
/// Grant, and Introduce cross-cell effect families.
#[derive(Serialize)]
pub struct BilateralPiView {
    pub outgoing_transfer_root: String,
    pub outgoing_grant_root: String,
    pub outgoing_introduce_root: String,
    pub incoming_transfer_root: String,
    pub incoming_grant_root: String,
    pub incoming_introduce_root: String,
}

// ---------------------------------------------------------------------------
// Refactor 6: cell program view types
// ---------------------------------------------------------------------------

/// Top-level view of a cell's program (Refactor 6).
#[derive(Serialize)]
#[serde(tag = "kind")]
pub enum CellProgramView {
    /// No program — any authorized state change is valid.
    None,
    /// Predicate program: a list of slot-caveat constraints (implicit AND).
    Predicate {
        constraints: Vec<StateConstraintView>,
    },
    /// Cases program: operation-scoped cases with guards.
    Cases { cases: Vec<TransitionCaseView> },
    /// Circuit program: an AIR/R1CS circuit identified by its VK hash.
    Circuit { circuit_hash: String },
}

/// Per-case view in a Cases program.
#[derive(Serialize)]
pub struct TransitionCaseView {
    pub guard: TransitionGuardView,
    pub constraints: Vec<StateConstraintView>,
}

/// TransitionGuard view.
#[derive(Serialize)]
#[serde(tag = "kind")]
pub enum TransitionGuardView {
    Always,
    MethodIs { method: String },
    EffectKindIs { mask: u32 },
    SlotChanged { index: u8 },
    AnyOf { children: Vec<TransitionGuardView> },
    AllOf { children: Vec<TransitionGuardView> },
}

/// Per-variant view for each StateConstraint (21+ variants).
/// Uses a tagged-union shape so JS can switch on `kind`.
#[derive(Serialize)]
#[serde(tag = "kind")]
pub enum StateConstraintView {
    FieldEquals {
        index: u8,
        value: String,
    },
    FieldGte {
        index: u8,
        value: String,
    },
    FieldLte {
        index: u8,
        value: String,
    },
    FieldLteField {
        left_index: u8,
        right_index: u8,
    },
    SumEquals {
        indices: Vec<u8>,
        value: String,
    },
    WriteOnce {
        index: u8,
    },
    Immutable {
        index: u8,
    },
    Monotonic {
        index: u8,
    },
    StrictMonotonic {
        index: u8,
    },
    BoundedBy {
        index: u8,
        witness_index: u8,
    },
    FieldDelta {
        index: u8,
        delta: String,
    },
    FieldDeltaInRange {
        index: u8,
        min_delta: String,
        max_delta: String,
    },
    FieldGteHeight {
        index: u8,
        offset: i64,
    },
    FieldLteHeight {
        index: u8,
        offset: i64,
    },
    SumEqualsAcross {
        input_fields: Vec<u8>,
        output_fields: Vec<u8>,
    },
    SenderAuthorized {
        set_kind: String,
        commitment: String,
    },
    CapabilityUniqueness {
        cap_set_root_slot: u8,
    },
    RateLimit {
        max_per_epoch: u32,
        epoch_duration: u64,
    },
    RateLimitBySum {
        slot_index: u8,
        max_sum_per_epoch: u64,
        epoch_duration: u64,
    },
    TemporalGate {
        not_before: Option<u64>,
        not_after: Option<u64>,
    },
    PreimageGate {
        commitment_index: u8,
        hash_kind: String,
    },
    MonotonicSequence {
        seq_index: u8,
    },
    AllowedTransitions {
        slot_index: u8,
        allowed: Vec<(String, String)>,
    },
    TemporalPredicate {
        witness_index: u8,
        dsl_hash: String,
    },
    BoundDelta {
        local_slot: u8,
        peer_cell: String,
        peer_slot: u8,
        delta_relation: String,
    },
    AnyOf {
        variants: Vec<StateConstraintView>,
    },
    Witnessed {
        predicate_kind: String,
        commitment: String,
        input_ref: String,
        proof_witness_index: usize,
    },
    Renounced {
        set_kind: String,
        commitment: String,
    },
    Custom {
        ir_hash: String,
        descriptor_debug: String,
    },
}

fn cell_program_to_view(program: &CellProgram) -> CellProgramView {
    match program {
        CellProgram::None => CellProgramView::None,
        CellProgram::Predicate(constraints) => CellProgramView::Predicate {
            constraints: constraints.iter().map(state_constraint_to_view).collect(),
        },
        CellProgram::Cases(cases) => CellProgramView::Cases {
            cases: cases.iter().map(transition_case_to_view).collect(),
        },
        CellProgram::Circuit { circuit_hash } => CellProgramView::Circuit {
            circuit_hash: hex_encode(circuit_hash),
        },
    }
}

fn transition_case_to_view(case: &TransitionCase) -> TransitionCaseView {
    TransitionCaseView {
        guard: transition_guard_to_view(&case.guard),
        constraints: case
            .constraints
            .iter()
            .map(state_constraint_to_view)
            .collect(),
    }
}

fn transition_guard_to_view(guard: &TransitionGuard) -> TransitionGuardView {
    match guard {
        TransitionGuard::Always => TransitionGuardView::Always,
        TransitionGuard::MethodIs { method } => TransitionGuardView::MethodIs {
            method: hex_encode(method),
        },
        TransitionGuard::EffectKindIs { mask } => TransitionGuardView::EffectKindIs { mask: *mask },
        TransitionGuard::SlotChanged { index } => {
            TransitionGuardView::SlotChanged { index: *index }
        }
        TransitionGuard::AnyOf(children) => TransitionGuardView::AnyOf {
            children: children.iter().map(transition_guard_to_view).collect(),
        },
        TransitionGuard::AllOf(children) => TransitionGuardView::AllOf {
            children: children.iter().map(transition_guard_to_view).collect(),
        },
    }
}

fn state_constraint_to_view(sc: &StateConstraint) -> StateConstraintView {
    match sc {
        StateConstraint::FieldEquals { index, value } => StateConstraintView::FieldEquals {
            index: *index,
            value: hex_encode(value),
        },
        StateConstraint::FieldGte { index, value } => StateConstraintView::FieldGte {
            index: *index,
            value: hex_encode(value),
        },
        StateConstraint::FieldLte { index, value } => StateConstraintView::FieldLte {
            index: *index,
            value: hex_encode(value),
        },
        StateConstraint::FieldLteField {
            left_index,
            right_index,
        } => StateConstraintView::FieldLteField {
            left_index: *left_index,
            right_index: *right_index,
        },
        StateConstraint::SumEquals { indices, value } => StateConstraintView::SumEquals {
            indices: indices.clone(),
            value: hex_encode(value),
        },
        StateConstraint::WriteOnce { index } => StateConstraintView::WriteOnce { index: *index },
        StateConstraint::Immutable { index } => StateConstraintView::Immutable { index: *index },
        StateConstraint::Monotonic { index } => StateConstraintView::Monotonic { index: *index },
        StateConstraint::StrictMonotonic { index } => {
            StateConstraintView::StrictMonotonic { index: *index }
        }
        StateConstraint::BoundedBy {
            index,
            witness_index,
        } => StateConstraintView::BoundedBy {
            index: *index,
            witness_index: *witness_index,
        },
        StateConstraint::FieldDelta { index, delta } => StateConstraintView::FieldDelta {
            index: *index,
            delta: hex_encode(delta),
        },
        StateConstraint::FieldDeltaInRange {
            index,
            min_delta,
            max_delta,
        } => StateConstraintView::FieldDeltaInRange {
            index: *index,
            min_delta: hex_encode(min_delta),
            max_delta: hex_encode(max_delta),
        },
        StateConstraint::FieldGteHeight { index, offset } => StateConstraintView::FieldGteHeight {
            index: *index,
            offset: *offset,
        },
        StateConstraint::FieldLteHeight { index, offset } => StateConstraintView::FieldLteHeight {
            index: *index,
            offset: *offset,
        },
        StateConstraint::SumEqualsAcross {
            input_fields,
            output_fields,
        } => StateConstraintView::SumEqualsAcross {
            input_fields: input_fields.clone(),
            output_fields: output_fields.clone(),
        },
        StateConstraint::SenderAuthorized { set } => {
            let (set_kind, commitment) = match set {
                AuthorizedSet::PublicRoot { set_root_index } => (
                    format!("PublicRoot(slot={set_root_index})"),
                    "from_slot".to_string(),
                ),
                AuthorizedSet::BlindedSet { commitment } => {
                    ("BlindedSet".to_string(), hex_encode(commitment))
                }
                AuthorizedSet::CredentialSet {
                    issuer_cell,
                    credential_schema_id,
                } => (
                    "CredentialSet".to_string(),
                    format!(
                        "issuer={} schema={}",
                        &hex_encode(issuer_cell)[..8],
                        &hex_encode(credential_schema_id)[..8]
                    ),
                ),
            };
            StateConstraintView::SenderAuthorized {
                set_kind,
                commitment,
            }
        }
        StateConstraint::CapabilityUniqueness { cap_set_root_slot } => {
            StateConstraintView::CapabilityUniqueness {
                cap_set_root_slot: *cap_set_root_slot,
            }
        }
        StateConstraint::RateLimit {
            max_per_epoch,
            epoch_duration,
        } => StateConstraintView::RateLimit {
            max_per_epoch: *max_per_epoch,
            epoch_duration: *epoch_duration,
        },
        StateConstraint::RateLimitBySum {
            slot_index,
            max_sum_per_epoch,
            epoch_duration,
        } => StateConstraintView::RateLimitBySum {
            slot_index: *slot_index,
            max_sum_per_epoch: *max_sum_per_epoch,
            epoch_duration: *epoch_duration,
        },
        StateConstraint::TemporalGate {
            not_before,
            not_after,
        } => StateConstraintView::TemporalGate {
            not_before: *not_before,
            not_after: *not_after,
        },
        StateConstraint::PreimageGate {
            commitment_index,
            hash_kind,
        } => StateConstraintView::PreimageGate {
            commitment_index: *commitment_index,
            hash_kind: match hash_kind {
                HashKind::Poseidon2 => "Poseidon2".to_string(),
                HashKind::Blake3 => "Blake3".to_string(),
            },
        },
        StateConstraint::MonotonicSequence { seq_index } => {
            StateConstraintView::MonotonicSequence {
                seq_index: *seq_index,
            }
        }
        StateConstraint::AllowedTransitions {
            slot_index,
            allowed,
        } => StateConstraintView::AllowedTransitions {
            slot_index: *slot_index,
            allowed: allowed
                .iter()
                .map(|(old, new)| (hex_encode(old), hex_encode(new)))
                .collect(),
        },
        StateConstraint::TemporalPredicate {
            witness_index,
            dsl_hash,
        } => StateConstraintView::TemporalPredicate {
            witness_index: *witness_index,
            dsl_hash: hex_encode(dsl_hash),
        },
        StateConstraint::BoundDelta {
            local_slot,
            peer_cell,
            peer_slot,
            delta_relation,
        } => StateConstraintView::BoundDelta {
            local_slot: *local_slot,
            peer_cell: hex_encode(&peer_cell.0),
            peer_slot: *peer_slot,
            delta_relation: format!("{delta_relation:?}"),
        },
        StateConstraint::AnyOf { variants } => {
            // SimpleStateConstraint subset — project each to a StateConstraintView
            // via the Debug representation for unsupported variants.
            StateConstraintView::AnyOf {
                variants: variants.iter().map(|v| simple_sc_to_view(v)).collect(),
            }
        }
        StateConstraint::Witnessed { wp } => StateConstraintView::Witnessed {
            predicate_kind: witnessed_predicate_kind_name(&wp.kind),
            commitment: hex_encode(&wp.commitment),
            input_ref: input_ref_name(&wp.input_ref),
            proof_witness_index: wp.proof_witness_index,
        },
        StateConstraint::Renounced { set } => {
            use dregg_cell::program::RenouncedSet;
            let (set_kind, commitment) = match set {
                RenouncedSet::PublicRoot { set_root_index } => (
                    format!("PublicRoot(slot={set_root_index})"),
                    "from_slot".to_string(),
                ),
                RenouncedSet::BlindedSet { commitment } => {
                    ("BlindedSet".to_string(), hex_encode(commitment))
                }
            };
            StateConstraintView::Renounced {
                set_kind,
                commitment,
            }
        }
        StateConstraint::Custom {
            ir_hash,
            descriptor,
            reads: _,
        } => StateConstraintView::Custom {
            ir_hash: hex_encode(ir_hash),
            descriptor_debug: format!("{descriptor:?}"),
        },
    }
}

fn simple_sc_to_view(sc: &dregg_cell::program::SimpleStateConstraint) -> StateConstraintView {
    use dregg_cell::program::SimpleStateConstraint;
    match sc {
        SimpleStateConstraint::FieldEquals { index, value } => StateConstraintView::FieldEquals {
            index: *index,
            value: hex_encode(value),
        },
        SimpleStateConstraint::FieldGte { index, value } => StateConstraintView::FieldGte {
            index: *index,
            value: hex_encode(value),
        },
        SimpleStateConstraint::FieldLte { index, value } => StateConstraintView::FieldLte {
            index: *index,
            value: hex_encode(value),
        },
        SimpleStateConstraint::WriteOnce { index } => {
            StateConstraintView::WriteOnce { index: *index }
        }
        SimpleStateConstraint::Immutable { index } => {
            StateConstraintView::Immutable { index: *index }
        }
        SimpleStateConstraint::Monotonic { index } => {
            StateConstraintView::Monotonic { index: *index }
        }
        SimpleStateConstraint::StrictMonotonic { index } => {
            StateConstraintView::StrictMonotonic { index: *index }
        }
        SimpleStateConstraint::BoundedBy {
            index,
            witness_index,
        } => StateConstraintView::BoundedBy {
            index: *index,
            witness_index: *witness_index,
        },
        SimpleStateConstraint::FieldGteHeight { index, offset } => {
            StateConstraintView::FieldGteHeight {
                index: *index,
                offset: *offset,
            }
        }
        SimpleStateConstraint::FieldLteHeight { index, offset } => {
            StateConstraintView::FieldLteHeight {
                index: *index,
                offset: *offset,
            }
        }
        SimpleStateConstraint::TemporalGate {
            not_before,
            not_after,
        } => StateConstraintView::TemporalGate {
            not_before: *not_before,
            not_after: *not_after,
        },
        SimpleStateConstraint::Not(inner) => {
            // Project Not as a FieldEquals with special marker value
            // (v0: Debug repr until we have a dedicated variant).
            StateConstraintView::FieldEquals {
                index: 255,
                value: format!("Not({:?})", inner),
            }
        }
    }
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

/// Return the current dregg-observability event log as the Studio wire JSON
/// (schema with "schema_version", "events": [{kind, envelope, payload}, ...]).
/// This is the source for the signal-cached getter in runtime-in-memory.js
/// and the <dregg-activity> live feed inspector (Task #30).
///
/// The log contains TurnLifecycle (at minimum; full 7 variants when deeper
/// executor hooks land) plus any future Authorization etc. events.
#[wasm_bindgen]
pub fn get_trace_events_json(handle: usize) -> Result<JsValue, JsError> {
    with_runtime_ref(handle, |rt| {
        let v = rt.events.to_json_value();
        serde_wasm_bindgen::to_value(&v).map_err(|e| e.to_string())
    })
}

/// Export runtime snapshot stub (STARBRIDGE-FOLLOWUP-03 on blocked §5.9).
///
/// Returns pretty JSON with current state summary + explicit note that
/// this is a v0 placeholder pending the canonical WitnessedReceipt stream
/// format (Houyhnhnm + plan §8 Q4). Unblocks JS/inspector prep for
/// snapshot-and-replay / time-travel without requiring the human cargo
/// session for proving changes. Matches the Rust surface added to
/// DreggRuntime::export_runtime_snapshot_stub.
///
/// Safe thin binding (delegates only; no new crypto, no circuit).
#[wasm_bindgen]
pub fn export_runtime_snapshot_stub(handle: usize) -> Result<String, JsError> {
    with_runtime_ref(handle, |rt| Ok(rt.export_runtime_snapshot_stub()))
}

/// Attempt time-travel rewind on the sim runtime (STARBRIDGE-FOLLOWUP-03
/// on blocked §5.10 + Q4).
///
/// For target <= current: returns Ok(()) only for exact current (no-op) or
/// Err explaining the pending snapshot format dependency.
/// For target > current: explicit forward-only error.
///
/// Provides the JS-callable surface + error shape for `<dregg-...>`
/// scrubber / cursor UI to target. `caps.timeTravel` should stay false
/// in surfaces until real impl lands. See runtime.rs docs and plan §5.10.
///
/// Thin + safe (no proving stack, delegates to stub).
#[wasm_bindgen]
pub fn attempt_time_travel(handle: usize, target_height: u64) -> Result<JsValue, JsError> {
    with_runtime(handle, |rt| match rt.time_travel_to_stub(target_height) {
        Ok(()) => {
            #[derive(Serialize)]
            struct TravelOk {
                success: bool,
                height: u64,
                note: String,
            }
            let res = TravelOk {
                success: true,
                height: rt.current_height,
                note: "no-op (already at target or within stub rules)".to_string(),
            };
            serde_wasm_bindgen::to_value(&res).map_err(|e| e.to_string())
        }
        Err(e) => {
            #[derive(Serialize)]
            struct TravelErr {
                success: bool,
                error: String,
                current_height: u64,
            }
            let res = TravelErr {
                success: false,
                error: e,
                current_height: rt.current_height,
            };
            serde_wasm_bindgen::to_value(&res).map_err(|e| e.to_string())
        }
    })
}

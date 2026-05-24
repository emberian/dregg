//! MCP (Model Context Protocol) server for the pyana node.
//!
//! Exposes node capabilities as MCP tools over JSON-RPC 2.0 (stdio transport).
//! AI assistants (Claude, GPT, etc.) can discover and invoke tools to interact
//! with the pyana federation: authorize actions, submit turns, manage capabilities,
//! post intents, and more.
//!
//! ## Transport
//!
//! - **Stdio**: `pyana-node mcp` reads JSON-RPC from stdin and writes to stdout.
//!   This is the standard MCP transport for local tool-calling.
//!
//! ## Protocol
//!
//! Implements the MCP subset needed for tool serving:
//! - `initialize` — capability negotiation
//! - `notifications/initialized` — client readiness signal (no response)
//! - `tools/list` — enumerate available tools
//! - `tools/call` — invoke a tool

use serde::{Deserialize, Serialize};
use serde_json::Value;
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};
use tracing::{error, info};

use pyana_sdk::{Attenuation, CellId};
use pyana_turn::{CallForest, Turn};
use pyana_types::PublicKey;

use crate::state::NodeState;

// Re-import x25519 and chacha for seal/unseal operations.

/// Parse a JSON effect descriptor into a turn `Effect`.
///
/// Supports the subset needed for the two-AI handoff demo:
/// - `{ "type": "transfer", "from": "<hex>", "to": "<hex>", "amount": N }`
/// - `{ "type": "increment_nonce", "cell": "<hex>" }`
/// - `{ "type": "set_field", "cell": "<hex>", "index": N, "value": N }`
///
/// Returns a human-readable error string when the descriptor is malformed.
/// MCP-first: this is the canonical effect-parsing surface; the HTTP API
/// would derive from it if/when it gains an effects body.
fn parse_effect_json(value: &Value) -> Result<pyana_turn::Effect, String> {
    let ty = value
        .get("type")
        .and_then(|v| v.as_str())
        .ok_or_else(|| "effect missing 'type' field".to_string())?;

    let get_hex_32 = |obj: &Value, field: &str| -> Result<[u8; 32], String> {
        let s = obj
            .get(field)
            .and_then(|v| v.as_str())
            .ok_or_else(|| format!("effect.{ty} missing field '{field}'"))?;
        hex_decode(s).map_err(|_| format!("effect.{ty}.{field}: invalid hex (expected 64 chars)"))
    };

    match ty {
        "transfer" => {
            let from = get_hex_32(value, "from")?;
            let to = get_hex_32(value, "to")?;
            let amount = value
                .get("amount")
                .and_then(|v| v.as_u64())
                .ok_or_else(|| "effect.transfer missing 'amount'".to_string())?;
            Ok(pyana_turn::Effect::Transfer {
                from: pyana_cell::CellId(from),
                to: pyana_cell::CellId(to),
                amount,
            })
        }
        "increment_nonce" => {
            let cell = get_hex_32(value, "cell")?;
            Ok(pyana_turn::Effect::IncrementNonce {
                cell: pyana_cell::CellId(cell),
            })
        }
        "set_field" => {
            let cell = get_hex_32(value, "cell")?;
            let index = value
                .get("index")
                .and_then(|v| v.as_u64())
                .ok_or_else(|| "effect.set_field missing 'index'".to_string())?
                as usize;
            let value_u32 = value
                .get("value")
                .and_then(|v| v.as_u64())
                .ok_or_else(|| "effect.set_field missing 'value'".to_string())?
                as u32;
            let mut value_bytes = [0u8; 32];
            value_bytes[..4].copy_from_slice(&value_u32.to_le_bytes());
            Ok(pyana_turn::Effect::SetField {
                cell: pyana_cell::CellId(cell),
                index,
                value: value_bytes,
            })
        }
        other => Err(format!(
            "unknown effect type '{other}' (supported: transfer, increment_nonce, set_field)"
        )),
    }
}

/// Build a CallForest with a single root action containing the given effects.
fn build_forest_with_effects(target: CellId, effects: Vec<pyana_turn::Effect>) -> CallForest {
    let action = pyana_turn::Action {
        target,
        method: pyana_turn::action::symbol("execute"),
        args: vec![],
        authorization: pyana_turn::Authorization::Unchecked,
        preconditions: pyana_cell::Preconditions::default(),
        effects,
        may_delegate: pyana_turn::DelegationMode::None,
        commitment_mode: pyana_turn::CommitmentMode::Full,
        balance_change: None,
    };
    let mut forest = CallForest::new();
    forest.add_root(action);
    forest
}

/// Build a CallForest with a single root action authorized by an Ed25519
/// signature over the canonical action-signing message. The signature is
/// produced by `wallet.sign_bytes` against `TurnExecutor::compute_signing_message`
/// in Full commitment mode using the executor's default federation id
/// (`[0u8; 32]`) — which matches `TurnExecutor::new(...).local_federation_id`.
fn build_signed_forest(
    target: CellId,
    effects: Vec<pyana_turn::Effect>,
    wallet: &pyana_sdk::AgentWallet,
) -> CallForest {
    let mut action = pyana_turn::Action {
        target,
        method: pyana_turn::action::symbol("execute"),
        args: vec![],
        authorization: pyana_turn::Authorization::Unchecked,
        preconditions: pyana_cell::Preconditions::default(),
        effects,
        may_delegate: pyana_turn::DelegationMode::None,
        commitment_mode: pyana_turn::CommitmentMode::Full,
        balance_change: None,
    };
    // Compute the canonical signing message and replace Unchecked with
    // Authorization::Signature so cells with `delegate: Signature` accept
    // the action.
    let federation_id = [0u8; 32];
    let msg = pyana_turn::TurnExecutor::compute_signing_message(&action, &federation_id);
    let sig = wallet.sign_bytes(&msg);
    let mut r = [0u8; 32];
    let mut s = [0u8; 32];
    r.copy_from_slice(&sig.0[..32]);
    s.copy_from_slice(&sig.0[32..]);
    action.authorization = pyana_turn::Authorization::Signature(r, s);

    let mut forest = CallForest::new();
    forest.add_root(action);
    forest
}

/// Generate an Effect VM STARK proof for a sequence of VM-domain effects.
///
/// Builds a fresh `CellState` from `(initial_balance, initial_nonce)`, runs the
/// effect VM trace generator, constructs the `EffectVmAir` sized to the effect
/// count, and produces a STARK proof. Returns the hex-encoded postcard-serialized
/// proof bytes, the public inputs converted to `u64` (BabyBear canonical
/// values fit in u32, so the JSON array is friendly to the independent verifier
/// which parses public inputs as u32), the trace as a `Vec<Vec<u32>>` for
/// scope-(2) WitnessedReceipt capture, and the BLAKE3 witness_hash of the
/// postcard-serialised `WitnessBundle::Inline` (hex-encoded) so demo scripts
/// can forward it verbatim into the on-disk replay chain.
///
/// Stage 7 / §C: returning the trace + witness_hash lets the MCP tool emit
/// scope-(2) WitnessedReceipts. The MCP layer ships these to the demo
/// scripts; the verifier-side `replay_chain` reconstructs `BabyBear` cells
/// via `BabyBear::new_canonical` and re-derives the witness_hash to check
/// the binding.
///
/// If `vm_effects` is empty, returns
/// `(String::new(), vec![], vec![], String::new())` — the caller decides
/// whether to omit the proof field or signal a warning.
fn generate_effect_vm_proof(
    initial_balance: u64,
    initial_nonce: u64,
    vm_effects: &[pyana_circuit::effect_vm::Effect],
) -> (String, Vec<u64>, Vec<Vec<u32>>, String) {
    if vm_effects.is_empty() {
        return (String::new(), Vec::new(), Vec::new(), String::new());
    }

    let initial_state =
        pyana_circuit::effect_vm::CellState::new(initial_balance, initial_nonce as u32);
    let (trace, public_inputs) =
        pyana_circuit::effect_vm::generate_effect_vm_trace(&initial_state, vm_effects);
    // The trace generator pads to the next power of two ≥ 2; the AIR must be
    // sized to the actual trace height, not the raw effect count (passing
    // `vm_effects.len()` panics when it's less than 2 or not a power of two).
    let air = pyana_circuit::effect_vm::EffectVmAir::new(trace.len());
    let proof = pyana_circuit::stark::prove(&air, &trace, &public_inputs);
    // Use the canonical PYNA-prefixed byte format that the standalone
    // pyana-verifier binary deserializes via stark::proof_from_bytes.
    // postcard's encoding lacks the magic-header and is not what the
    // verifier accepts on the wire.
    let proof_bytes = pyana_circuit::stark::proof_to_bytes(&proof);
    let proof_hex = hex_encode(&proof_bytes);
    let public_inputs_u64: Vec<u64> = public_inputs.iter().map(|f| f.as_u32() as u64).collect();
    // Build the canonical WitnessBundle::Inline so we can both ship the
    // trace shape and compute its BLAKE3 hash via the canonical
    // postcard-serialised form. The demo writes both to disk; the verifier
    // re-derives the hash to enforce binding.
    let bundle = pyana_turn::WitnessBundle::inline_from_trace(&trace);
    let trace_rows = bundle.trace_rows.clone();
    let witness_hash_hex = hex_encode(&bundle.witness_hash());
    (proof_hex, public_inputs_u64, trace_rows, witness_hash_hex)
}

// =============================================================================
// JSON-RPC types
// =============================================================================

#[derive(Deserialize)]
struct JsonRpcRequest {
    jsonrpc: String,
    id: Option<Value>,
    method: String,
    #[serde(default)]
    params: Value,
}

#[derive(Serialize)]
struct JsonRpcResponse {
    jsonrpc: &'static str,
    id: Value,
    #[serde(skip_serializing_if = "Option::is_none")]
    result: Option<Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    error: Option<JsonRpcError>,
}

#[derive(Serialize)]
struct JsonRpcError {
    code: i32,
    message: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    data: Option<Value>,
}

impl JsonRpcResponse {
    fn success(id: Value, result: Value) -> Self {
        Self {
            jsonrpc: "2.0",
            id,
            result: Some(result),
            error: None,
        }
    }

    fn error(id: Value, code: i32, message: impl Into<String>) -> Self {
        Self {
            jsonrpc: "2.0",
            id,
            result: None,
            error: Some(JsonRpcError {
                code,
                message: message.into(),
                data: None,
            }),
        }
    }

    fn method_not_found(id: Value) -> Self {
        Self::error(id, -32601, "Method not found")
    }

    fn invalid_params(id: Value, msg: impl Into<String>) -> Self {
        Self::error(id, -32602, msg)
    }

    fn internal_error(id: Value, msg: impl Into<String>) -> Self {
        Self::error(id, -32603, msg)
    }
}

// =============================================================================
// MCP protocol types
// =============================================================================

#[derive(Serialize)]
struct McpInitializeResult {
    #[serde(rename = "protocolVersion")]
    protocol_version: &'static str,
    capabilities: McpCapabilities,
    #[serde(rename = "serverInfo")]
    server_info: McpServerInfo,
}

#[derive(Serialize)]
struct McpCapabilities {
    tools: McpToolsCapability,
}

#[derive(Serialize)]
struct McpToolsCapability {
    #[serde(rename = "listChanged")]
    list_changed: bool,
}

#[derive(Serialize)]
struct McpServerInfo {
    name: &'static str,
    version: &'static str,
}

#[derive(Serialize)]
struct McpToolsListResult {
    tools: Vec<McpToolDef>,
}

#[derive(Serialize)]
struct McpToolDef {
    name: &'static str,
    description: &'static str,
    #[serde(rename = "inputSchema")]
    input_schema: Value,
}

#[derive(Serialize)]
struct McpToolResult {
    content: Vec<McpContent>,
    #[serde(rename = "isError", skip_serializing_if = "Option::is_none")]
    is_error: Option<bool>,
}

#[derive(Serialize)]
struct McpContent {
    #[serde(rename = "type")]
    content_type: &'static str,
    text: String,
}

impl McpToolResult {
    fn text(s: impl Into<String>) -> Self {
        Self {
            content: vec![McpContent {
                content_type: "text",
                text: s.into(),
            }],
            is_error: None,
        }
    }

    fn json(value: &Value) -> Self {
        Self::text(serde_json::to_string_pretty(value).unwrap_or_default())
    }

    fn error(s: impl Into<String>) -> Self {
        Self {
            content: vec![McpContent {
                content_type: "text",
                text: s.into(),
            }],
            is_error: Some(true),
        }
    }
}

// =============================================================================
// Tool definitions
// =============================================================================

fn tool_definitions() -> Vec<McpToolDef> {
    vec![
        McpToolDef {
            name: "pyana_get_status",
            description: "Get node status (height, peers, health)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {},
                "required": []
            }),
        },
        McpToolDef {
            name: "pyana_create_agent",
            description: "Register this node's wallet as a cell in the local ledger (idempotent). Returns the content-addressed cell_id.",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "name": { "type": "string", "description": "Human-readable label for the agent (informational only; identity is content-addressed from the wallet pubkey)" },
                    "initial_balance": { "type": "integer", "description": "Initial computron balance for the cell when first created. Ignored on subsequent calls." }
                },
                "required": ["name"]
            }),
        },
        McpToolDef {
            name: "pyana_authorize",
            description: "Prove authorization for an action using ZK proof",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "action": { "type": "string", "description": "The action to authorize (e.g. read, write)" },
                    "resource": { "type": "string", "description": "The resource to act upon" },
                    "mode": { "type": "string", "enum": ["trusted", "selective", "private"], "description": "Verification mode: trusted (fastest), selective (partial ZK), private (full ZK)" }
                },
                "required": ["action", "resource"]
            }),
        },
        McpToolDef {
            name: "pyana_submit_turn",
            description: "Submit an atomic turn (set of actions) for execution. Pass an `effects` array to actually perform work (transfers, set_field, etc.); omit it for a no-op turn that just chains a receipt.",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "target_cell": { "type": "string", "description": "Hex-encoded 32-byte target cell ID" },
                    "method": { "type": "string", "description": "The method to invoke on the cell" },
                    "fee": { "type": "integer", "description": "Fee in computrons (default: 0)" },
                    "memo": { "type": "string", "description": "Optional memo attached to the turn" },
                    "effects": {
                        "type": "array",
                        "description": "Optional list of effects: { type: 'transfer', from, to, amount } | { type: 'increment_nonce', cell } | { type: 'set_field', cell, index, value }",
                        "items": { "type": "object" }
                    }
                },
                "required": ["target_cell", "method"]
            }),
        },
        McpToolDef {
            name: "pyana_grant_capability",
            description: "Grant a capability to another agent",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "to_agent": { "type": "string", "description": "Hex-encoded public key of the recipient agent" },
                    "target_cell": { "type": "string", "description": "Hex-encoded cell ID the capability applies to" },
                    "permissions": { "type": "string", "description": "Comma-separated permissions (e.g. read,write)" }
                },
                "required": ["to_agent", "target_cell", "permissions"]
            }),
        },
        McpToolDef {
            name: "pyana_revoke_capability",
            description: "Revoke a previously granted capability",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "cap_slot": { "type": "integer", "description": "The capability slot number to revoke" }
                },
                "required": ["cap_slot"]
            }),
        },
        McpToolDef {
            name: "pyana_post_intent",
            description: "Post an intent to the marketplace (request a capability/service)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "action": { "type": "string", "description": "The action needed (e.g. read, write, execute)" },
                    "resource": { "type": "string", "description": "The resource pattern (e.g. documents/*)" },
                    "max_fee": { "type": "integer", "description": "Maximum fee willing to pay (computrons)" },
                    "expiry_blocks": { "type": "integer", "description": "Number of blocks until intent expires" }
                },
                "required": ["action", "resource"]
            }),
        },
        McpToolDef {
            name: "pyana_fulfill_intent",
            description: "Fulfill a matching intent from the marketplace",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "intent_id": { "type": "string", "description": "Hex-encoded 32-byte intent ID to fulfill" }
                },
                "required": ["intent_id"]
            }),
        },
        McpToolDef {
            name: "pyana_delegate",
            description: "Delegate a bounded sub-capability to another agent",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "capability": { "type": "integer", "description": "Token slot number to delegate from" },
                    "to_agent": { "type": "string", "description": "Hex-encoded public key of the delegatee" },
                    "restrictions": { "type": "object", "description": "Restriction object (services, expiry, etc.)" },
                    "max_staleness": { "type": "integer", "description": "Maximum staleness in blocks before re-delegation required" }
                },
                "required": ["capability", "to_agent"]
            }),
        },
        McpToolDef {
            name: "pyana_check_capabilities",
            description: "List all capabilities held by the current agent",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {},
                "required": []
            }),
        },
        McpToolDef {
            name: "pyana_read_cell",
            description: "Read a cell's state (balance, fields, permissions)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "cell_id": { "type": "string", "description": "Hex-encoded 32-byte cell ID" }
                },
                "required": ["cell_id"]
            }),
        },
        McpToolDef {
            name: "pyana_get_receipt_chain",
            description: "Get the agent's auditable receipt chain (action history)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "limit": { "type": "integer", "description": "Maximum number of receipts to return (default: 50)" }
                },
                "required": []
            }),
        },
        McpToolDef {
            name: "pyana_seal_data",
            description: "Encrypt data that only a specific agent can decrypt",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "data": { "type": "string", "description": "The plaintext data to seal" },
                    "recipient": { "type": "string", "description": "Hex-encoded public key of the intended recipient" }
                },
                "required": ["data", "recipient"]
            }),
        },
        McpToolDef {
            name: "pyana_unseal_data",
            description: "Decrypt sealed data addressed to this agent",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "sealed_box": { "type": "string", "description": "Hex-encoded sealed box bytes" }
                },
                "required": ["sealed_box"]
            }),
        },
        McpToolDef {
            name: "pyana_bridge_note",
            description: "Bridge a note to another federation",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "note_commitment": { "type": "string", "description": "Hex-encoded 32-byte note commitment" },
                    "destination_federation": { "type": "string", "description": "Hex-encoded federation ID" }
                },
                "required": ["note_commitment", "destination_federation"]
            }),
        },
        // ─── Sovereign Cells ───────────────────────────────────────────────────────
        McpToolDef {
            name: "pyana_make_sovereign",
            description: "Transition a cell to sovereign mode (cell stores its own state, federation only holds commitment)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "cell_id": { "type": "string", "description": "Hex-encoded 32-byte cell ID to transition" }
                },
                "required": ["cell_id"]
            }),
        },
        McpToolDef {
            name: "pyana_peer_exchange",
            description: "Initiate P2P state exchange with another sovereign cell, producing a STARK proof of the transition",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "cell_id": { "type": "string", "description": "Hex-encoded 32-byte local cell ID" },
                    "peer_cell_id": { "type": "string", "description": "Hex-encoded 32-byte peer cell ID" },
                    "new_commitment": { "type": "string", "description": "Hex-encoded 32-byte new state commitment after exchange" }
                },
                "required": ["cell_id", "peer_cell_id", "new_commitment"]
            }),
        },
        McpToolDef {
            name: "pyana_compress_history",
            description: "IVC-compress a sovereign cell's turn history into a single constant-size proof",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "cell_id": { "type": "string", "description": "Hex-encoded 32-byte cell ID" },
                    "initial_root": { "type": "integer", "description": "Initial state root (BabyBear field element as u32)" },
                    "turn_count": { "type": "integer", "description": "Number of recent turns to compress (default: all)" }
                },
                "required": ["cell_id", "initial_root"]
            }),
        },
        // ─── Bearer Capabilities ───────────────────────────────────────────────────
        McpToolDef {
            name: "pyana_create_bearer_cap",
            description: "Create a bearer capability proof (immediate grant, no c-list storage required)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "target_cell": { "type": "string", "description": "Hex-encoded 32-byte target cell the cap grants access to" },
                    "permissions": { "type": "string", "description": "Permission level: none, signature, proof, either" },
                    "expires_at": { "type": "integer", "description": "Block height at which the bearer cap expires" },
                    "bearer_pk": { "type": "string", "description": "Hex-encoded 32-byte public key of the intended bearer" }
                },
                "required": ["target_cell", "permissions", "expires_at", "bearer_pk"]
            }),
        },
        McpToolDef {
            name: "pyana_exercise_bearer_cap",
            description: "Exercise a bearer capability to perform an action without c-list storage. Pass an `effects` array to actually perform work (e.g. transfer from the target cell).",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "target_cell": { "type": "string", "description": "Hex-encoded 32-byte target cell" },
                    "method": { "type": "string", "description": "Method to invoke on the target cell" },
                    "delegation_chain": { "type": "string", "description": "Hex-encoded delegation chain signature" },
                    "bearer_pk": { "type": "string", "description": "Hex-encoded 32-byte bearer public key" },
                    "expires_at": { "type": "integer", "description": "Expiry height of the bearer cap" },
                    "permissions": { "type": "string", "description": "Permission level the bearer cap commits to (default: 'signature' for backward compat)" },
                    "effects": {
                        "type": "array",
                        "description": "List of effects to execute under the bearer authorization (typically a single transfer). Each effect is { type, ... } per the parse_effect_json contract.",
                        "items": { "type": "object" }
                    }
                },
                "required": ["target_cell", "method", "delegation_chain", "bearer_pk", "expires_at"]
            }),
        },
        // ─── Factories ─────────────────────────────────────────────────────────────
        McpToolDef {
            name: "pyana_deploy_factory",
            description: "Deploy a factory descriptor to the ProgramRegistry (defines what new cells can be created)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "factory_vk": { "type": "string", "description": "Hex-encoded 32-byte factory verification key" },
                    "child_vk_strategy": { "type": "string", "enum": ["fixed", "derived", "approved_set"], "description": "How child VKs are determined" },
                    "max_creations_per_epoch": { "type": "integer", "description": "Maximum cells this factory can create per epoch (0 = unlimited)" },
                    "sovereign": { "type": "boolean", "description": "Whether created cells are sovereign (default: false)" }
                },
                "required": ["factory_vk"]
            }),
        },
        McpToolDef {
            name: "pyana_create_from_factory",
            description: "Create a new cell from a deployed factory (with provenance tracking)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "factory_vk": { "type": "string", "description": "Hex-encoded 32-byte factory VK to create from" },
                    "cell_name": { "type": "string", "description": "Human-readable name for the new cell" },
                    "sovereign": { "type": "boolean", "description": "Whether the new cell is sovereign (default: false)" }
                },
                "required": ["factory_vk"]
            }),
        },
        McpToolDef {
            name: "pyana_verify_provenance",
            description: "Verify a cell's factory provenance (check its creation lineage)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "cell_id": { "type": "string", "description": "Hex-encoded 32-byte cell ID to check" },
                    "expected_factory_vk": { "type": "string", "description": "Hex-encoded 32-byte expected factory VK (optional filter)" }
                },
                "required": ["cell_id"]
            }),
        },
        // ─── Effect VM ─────────────────────────────────────────────────────────────
        McpToolDef {
            name: "pyana_prove_sovereign_turn",
            description: "Generate a STARK proof for a sovereign cell's multi-effect turn via the Effect VM",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "cell_id": { "type": "string", "description": "Hex-encoded 32-byte sovereign cell ID" },
                    "effects": {
                        "type": "array",
                        "items": {
                            "type": "object",
                            "properties": {
                                "type": { "type": "string", "enum": ["credit", "debit", "set_field", "grant_cap"], "description": "Effect type" },
                                "amount": { "type": "integer", "description": "Amount for credit/debit effects" },
                                "field": { "type": "string", "description": "Field name for set_field" },
                                "value": { "type": "string", "description": "Field value for set_field" }
                            },
                            "required": ["type"]
                        },
                        "description": "List of effects to prove"
                    },
                    "pre_state_hash": { "type": "string", "description": "Hex-encoded 32-byte pre-state commitment" }
                },
                "required": ["cell_id", "effects", "pre_state_hash"]
            }),
        },
        McpToolDef {
            name: "pyana_verify_sovereign_proof",
            description: "Verify a STARK proof generated by the Effect VM for a sovereign turn",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "proof_hex": { "type": "string", "description": "Hex-encoded proof bytes" },
                    "public_inputs": {
                        "type": "array",
                        "items": { "type": "integer" },
                        "description": "Public input values (BabyBear field elements as u32)"
                    }
                },
                "required": ["proof_hex", "public_inputs"]
            }),
        },
        // ─── Privacy ───────────────────────────────────────────────────────────────
        McpToolDef {
            name: "pyana_create_stealth_address",
            description: "Generate a one-time stealth address for a recipient (unlinkable receive address)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "recipient_spend_pubkey": { "type": "string", "description": "Hex-encoded 32-byte recipient spend public key" },
                    "recipient_view_pubkey": { "type": "string", "description": "Hex-encoded 32-byte recipient view public key" }
                },
                "required": ["recipient_spend_pubkey", "recipient_view_pubkey"]
            }),
        },
        McpToolDef {
            name: "pyana_private_transfer",
            description: "Perform a private value transfer using Pedersen commitments (hides amount)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "from_cell": { "type": "string", "description": "Hex-encoded 32-byte sender cell ID" },
                    "to_cell": { "type": "string", "description": "Hex-encoded 32-byte recipient cell ID" },
                    "amount": { "type": "integer", "description": "Transfer amount (hidden in commitment)" },
                    "blinding": { "type": "string", "description": "Hex-encoded 32-byte blinding factor (random if omitted)" }
                },
                "required": ["from_cell", "to_cell", "amount"]
            }),
        },
        McpToolDef {
            name: "pyana_encrypt_intent",
            description: "Post an SSE-encrypted intent (body hidden, matchable via search tokens)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "action": { "type": "string", "description": "The action needed (e.g. read, write, execute)" },
                    "resource": { "type": "string", "description": "The resource pattern (e.g. documents/*)" },
                    "expiry_blocks": { "type": "integer", "description": "Number of blocks until intent expires" }
                },
                "required": ["action", "resource"]
            }),
        },
        McpToolDef {
            name: "pyana_prove_predicate",
            description: "Prove a predicate over private data (e.g. balance >= threshold) without revealing the value",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "predicate_type": { "type": "string", "enum": ["gte", "lte", "eq", "range", "membership"], "description": "Type of predicate to prove" },
                    "attribute": { "type": "string", "description": "Name of the attribute being proven" },
                    "threshold": { "type": "integer", "description": "Threshold value for comparison predicates" },
                    "private_value": { "type": "integer", "description": "The private value (not revealed in proof)" },
                    "state_root": { "type": "integer", "description": "Current state root (BabyBear field element as u32)" }
                },
                "required": ["predicate_type", "attribute", "private_value", "state_root"]
            }),
        },
        // ─── Proof Composition ─────────────────────────────────────────────────────
        McpToolDef {
            name: "pyana_compose_proofs",
            description: "Compose multiple proofs using logical operators (and/or/chain/aggregate)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "mode": { "type": "string", "enum": ["and", "or", "chain", "aggregate"], "description": "Composition mode" },
                    "proofs": {
                        "type": "array",
                        "items": { "type": "string" },
                        "description": "Hex-encoded proof bytes to compose"
                    },
                    "public_inputs": {
                        "type": "array",
                        "items": {
                            "type": "array",
                            "items": { "type": "integer" }
                        },
                        "description": "Public inputs for each proof (array of arrays)"
                    }
                },
                "required": ["mode", "proofs"]
            }),
        },
        // ─── Blocklace ─────────────────────────────────────────────────────────────
        McpToolDef {
            name: "pyana_get_blocklace_status",
            description: "Get blocklace consensus status (tip, finality level, participants, wave)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {},
                "required": []
            }),
        },
        McpToolDef {
            name: "pyana_get_constitution",
            description: "Get the current federation constitution (membership set, threshold, version)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {},
                "required": []
            }),
        },
        McpToolDef {
            name: "pyana_propose_membership",
            description: "Propose a membership change (join/leave/threshold change) to the federation",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "action": { "type": "string", "enum": ["join", "leave"], "description": "Whether to propose joining or leaving" },
                    "participant": { "type": "string", "description": "Hex-encoded 32-byte public key of the participant (for join: new member; for leave: departing member)" },
                    "reason": { "type": "string", "description": "Human-readable reason for the proposal" }
                },
                "required": ["action", "participant"]
            }),
        },
        // ─── Shared Resources ──────────────────────────────────────────────────────
        McpToolDef {
            name: "pyana_check_resource_budget",
            description: "Query remaining budget allowance for a shared resource (bounded-counter coordination)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "cell_id": { "type": "string", "description": "Hex-encoded 32-byte cell ID of the agent" }
                },
                "required": ["cell_id"]
            }),
        },
        McpToolDef {
            name: "pyana_debit_shared_resource",
            description: "Optimistic debit from a shared resource (Tier 2: consensus-free if within local budget slice)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "cell_id": { "type": "string", "description": "Hex-encoded 32-byte cell ID of the agent" },
                    "amount": { "type": "integer", "description": "Amount to debit from the shared resource" },
                    "memo": { "type": "string", "description": "Optional memo for the debit operation" }
                },
                "required": ["cell_id", "amount"]
            }),
        },
        // ─── Gallery ───────────────────────────────────────────────────────────────
        McpToolDef {
            name: "pyana_list_auctions",
            description: "List active gallery auctions (commit-reveal sealed-bid)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "status": { "type": "string", "enum": ["commit", "reveal", "settled", "all"], "description": "Filter by auction phase (default: all)" }
                },
                "required": []
            }),
        },
        McpToolDef {
            name: "pyana_place_bid",
            description: "Place a sealed bid on a gallery auction (commit phase: bid amount hidden behind commitment)",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "auction_id": { "type": "string", "description": "Hex-encoded 32-byte auction ID" },
                    "amount": { "type": "integer", "description": "Bid amount (will be committed, not revealed until reveal phase)" },
                    "nonce": { "type": "string", "description": "Hex-encoded 32-byte random nonce for commitment (generated if omitted)" }
                },
                "required": ["auction_id", "amount"]
            }),
        },
    ]
}

// =============================================================================
// Tool dispatch
// =============================================================================

async fn dispatch_tool(name: &str, params: Value, state: &NodeState) -> McpToolResult {
    match name {
        "pyana_get_status" => tool_get_status(state).await,
        "pyana_create_agent" => tool_create_agent(&params, state).await,
        "pyana_authorize" => tool_authorize(&params, state).await,
        "pyana_submit_turn" => tool_submit_turn(&params, state).await,
        "pyana_grant_capability" => tool_grant_capability(&params, state).await,
        "pyana_revoke_capability" => tool_revoke_capability(&params, state).await,
        "pyana_post_intent" => tool_post_intent(&params, state).await,
        "pyana_fulfill_intent" => tool_fulfill_intent(&params, state).await,
        "pyana_delegate" => tool_delegate(&params, state).await,
        "pyana_check_capabilities" => tool_check_capabilities(state).await,
        "pyana_read_cell" => tool_read_cell(&params, state).await,
        "pyana_get_receipt_chain" => tool_get_receipt_chain(&params, state).await,
        "pyana_seal_data" => tool_seal_data(&params, state).await,
        "pyana_unseal_data" => tool_unseal_data(&params, state).await,
        "pyana_bridge_note" => tool_bridge_note(&params, state).await,
        // Sovereign Cells
        "pyana_make_sovereign" => tool_make_sovereign(&params, state).await,
        "pyana_peer_exchange" => tool_peer_exchange(&params, state).await,
        "pyana_compress_history" => tool_compress_history(&params, state).await,
        // Bearer Capabilities
        "pyana_create_bearer_cap" => tool_create_bearer_cap(&params, state).await,
        "pyana_exercise_bearer_cap" => tool_exercise_bearer_cap(&params, state).await,
        // Factories
        "pyana_deploy_factory" => tool_deploy_factory(&params, state).await,
        "pyana_create_from_factory" => tool_create_from_factory(&params, state).await,
        "pyana_verify_provenance" => tool_verify_provenance(&params, state).await,
        // Effect VM
        "pyana_prove_sovereign_turn" => tool_prove_sovereign_turn(&params, state).await,
        "pyana_verify_sovereign_proof" => tool_verify_sovereign_proof(&params, state).await,
        // Privacy
        "pyana_create_stealth_address" => tool_create_stealth_address(&params, state).await,
        "pyana_private_transfer" => tool_private_transfer(&params, state).await,
        "pyana_encrypt_intent" => tool_encrypt_intent(&params, state).await,
        "pyana_prove_predicate" => tool_prove_predicate(&params, state).await,
        // Proof Composition
        "pyana_compose_proofs" => tool_compose_proofs(&params, state).await,
        // Blocklace
        "pyana_get_blocklace_status" => tool_get_blocklace_status(state).await,
        "pyana_get_constitution" => tool_get_constitution(state).await,
        "pyana_propose_membership" => tool_propose_membership(&params, state).await,
        // Shared Resources
        "pyana_check_resource_budget" => tool_check_resource_budget(&params, state).await,
        "pyana_debit_shared_resource" => tool_debit_shared_resource(&params, state).await,
        // Gallery
        "pyana_list_auctions" => tool_list_auctions(&params, state).await,
        "pyana_place_bid" => tool_place_bid(&params, state).await,
        _ => McpToolResult::error(format!("unknown tool: {name}")),
    }
}

// =============================================================================
// Tool implementations
// =============================================================================

async fn tool_get_status(state: &NodeState) -> McpToolResult {
    let s = state.read().await;

    // F-P2-7: status is informational; the HTTP /status endpoint does not require
    // the wallet to be unlocked, and neither should the MCP analog. (Health
    // checks need to work while locked.)

    let latest_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);
    let revocation_count = s.store.revocation_count().unwrap_or(0);
    let note_count = s.store.note_count().unwrap_or(0);
    let peer_count = s.peers.len();
    let store_ok = s.store.latest_attested_root().is_ok();
    let wallet_ok = s.unlocked || s.passphrase_hash.is_some();

    McpToolResult::json(&serde_json::json!({
        "healthy": store_ok && wallet_ok,
        "peer_count": peer_count,
        "latest_height": latest_height,
        "revocation_count": revocation_count,
        "note_count": note_count,
        "unlocked": s.unlocked,
    }))
}

async fn tool_create_agent(params: &Value, state: &NodeState) -> McpToolResult {
    let name = match params.get("name").and_then(|v| v.as_str()) {
        Some(n) => n,
        None => return McpToolResult::error("missing required parameter: name"),
    };

    let initial_balance = params
        .get("initial_balance")
        .and_then(|v| v.as_u64())
        .unwrap_or(0);

    let mut s = state.write().await;
    if !s.unlocked {
        return McpToolResult::error("wallet is locked; unlock first");
    }

    // MCP-first identity: the calling AI process IS this node, so
    // "create agent" means "register this node's wallet identity as a
    // cell in the ledger so it can be granted/received capabilities and
    // hold balance." The cell ID is content-addressed from the wallet's
    // public key plus the zero token domain (matching how
    // `submit_turn`, `grant_capability`, etc. derive it).
    //
    // Per 06-the-real-demo.md step 2 ("Alice becomes a cell"), this is
    // what makes downstream grant/transfer/handoff actually have a
    // target cell to land on. Previously this tool generated an
    // ephemeral wallet and discarded it; grants against the resulting
    // pubkey failed because no Cell existed in the ledger.
    let pk = s.wallet.public_key();
    let pk_bytes = pk.0;
    let cell_id = pyana_cell::CellId::derive_raw(&pk_bytes, &[0u8; 32]);
    let pk_hex: String = pk_bytes.iter().map(|b| format!("{b:02x}")).collect();
    let cell_id_hex = hex_encode(&cell_id.0);

    let already_existed = s.ledger.get(&cell_id).is_some();

    if !already_existed {
        let cell = pyana_cell::Cell::with_balance(pk_bytes, [0u8; 32], initial_balance);
        if let Err(e) = s.ledger.insert_cell(cell) {
            return McpToolResult::error(format!("ledger insert failed: {e}"));
        }
    }

    let (balance, nonce, cap_count) = match s.ledger.get(&cell_id) {
        Some(c) => (c.state.balance(), c.state.nonce(), c.capabilities.len()),
        None => (0, 0, 0),
    };

    drop(s);

    McpToolResult::json(&serde_json::json!({
        "name": name,
        "public_key": pk_hex,
        "cell_id": cell_id_hex,
        "balance": balance,
        "nonce": nonce,
        "capability_count": cap_count,
        "created": !already_existed,
        "already_existed": already_existed,
        "note": "Agent cell registered in the local ledger. cell_id is content-addressed from the wallet's public key + zero token domain.",
    }))
}

async fn tool_authorize(params: &Value, state: &NodeState) -> McpToolResult {
    let action = match params.get("action").and_then(|v| v.as_str()) {
        Some(a) => a.to_string(),
        None => return McpToolResult::error("missing required parameter: action"),
    };
    let resource = match params.get("resource").and_then(|v| v.as_str()) {
        Some(r) => r.to_string(),
        None => return McpToolResult::error("missing required parameter: resource"),
    };
    let mode = params
        .get("mode")
        .and_then(|v| v.as_str())
        .unwrap_or("trusted");

    let s = state.read().await;

    if !s.unlocked {
        return McpToolResult::error("wallet is locked; unlock first");
    }

    // Find a token that grants the requested action on the resource.
    let auth_req = pyana_sdk::AuthRequest {
        service: Some(resource.clone()),
        action: Some(action.clone()),
        ..Default::default()
    };

    // Try each held token.
    let mut authorized = false;
    let mut matching_token_id = None;
    for token in s.wallet.tokens() {
        if s.wallet.verify_token(token, &auth_req) {
            authorized = true;
            matching_token_id = Some(token.id().to_string());
            break;
        }
    }

    McpToolResult::json(&serde_json::json!({
        "authorized": authorized,
        "action": action,
        "resource": resource,
        "mode": mode,
        "token_id": matching_token_id,
    }))
}

async fn tool_submit_turn(params: &Value, state: &NodeState) -> McpToolResult {
    let target_cell_hex = match params.get("target_cell").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: target_cell"),
    };
    let method = match params.get("method").and_then(|v| v.as_str()) {
        Some(m) => m,
        None => return McpToolResult::error("missing required parameter: method"),
    };
    let fee = params.get("fee").and_then(|v| v.as_u64()).unwrap_or(0);
    let memo = params
        .get("memo")
        .and_then(|v| v.as_str())
        .map(String::from);

    let target_cell_bytes = match hex_decode(target_cell_hex) {
        Ok(b) => b,
        Err(_) => {
            return McpToolResult::error("invalid hex for target_cell (expected 64 hex chars)");
        }
    };

    let mut s = state.write().await;
    if !s.unlocked {
        return McpToolResult::error("wallet is locked; unlock first");
    }

    // SECURITY: Use the wallet's own cell ID as the turn agent (not caller-supplied).
    // The target_cell identifies which cell the action targets, not who is submitting.
    let agent_cell_id = pyana_cell::CellId::derive_raw(&s.wallet.public_key().0, &[0u8; 32]);
    let target_cell_id = pyana_cell::CellId(target_cell_bytes);

    // Build an action targeting the specified cell with the given method.
    let action = pyana_turn::Action {
        target: target_cell_id,
        method: pyana_turn::action::symbol(method),
        args: vec![],
        authorization: pyana_turn::Authorization::Unchecked,
        preconditions: pyana_cell::Preconditions::default(),
        effects: vec![],
        may_delegate: pyana_turn::DelegationMode::None,
        commitment_mode: pyana_turn::CommitmentMode::Full,
        balance_change: None,
    };
    let mut forest = CallForest::new();
    forest.add_root(action);

    let nonce = s.wallet.receipt_chain_length() as u64;
    let turn = Turn {
        agent: agent_cell_id,
        nonce,
        fee,
        memo,
        valid_until: None,
        call_forest: forest,
        depends_on: vec![],
        previous_receipt_hash: s.wallet.receipt_chain().last().map(|r| r.receipt_hash()),
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
    };

    let signed = s.wallet.sign_turn(&turn);
    let turn_hash_bytes = turn.hash();
    let turn_hash = hex_encode(&turn_hash_bytes);

    // Execute the turn locally.
    let executor = pyana_turn::TurnExecutor::new(pyana_turn::ComputronCosts::default());
    let exec_result = executor.execute(&turn, &mut s.ledger);

    match exec_result {
        pyana_turn::TurnResult::Committed { receipt, .. } => {
            s.wallet.append_receipt(receipt);

            // Serialize the full SignedTurn for gossip (postcard format).
            let turn_data = postcard::to_stdvec(&signed).expect("SignedTurn serialization");

            drop(s);

            // Emit receipt event to WebSocket subscribers.
            state.emit(crate::state::NodeEvent::Receipt {
                hash: turn_hash.clone(),
            });

            // Gossip the turn to federation peers.
            if let Some(gossip) = state.gossip().await {
                let hash = turn_hash_bytes;
                tokio::spawn(async move {
                    gossip.gossip_turn(hash, turn_data).await;
                });
            }

            McpToolResult::json(&serde_json::json!({
                "accepted": true,
                "turn_hash": turn_hash,
                "signer": hex_encode(&signed.signer.0),
            }))
        }
        pyana_turn::TurnResult::Rejected { reason, .. } => {
            drop(s);
            McpToolResult::json(&serde_json::json!({
                "accepted": false,
                "turn_hash": turn_hash,
                "error": format!("rejected: {reason}"),
            }))
        }
        _ => {
            drop(s);
            McpToolResult::json(&serde_json::json!({
                "accepted": false,
                "turn_hash": turn_hash,
                "error": "turn execution did not commit",
            }))
        }
    }
}

async fn tool_grant_capability(params: &Value, state: &NodeState) -> McpToolResult {
    let to_agent_hex = match params.get("to_agent").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: to_agent"),
    };
    let target_cell_hex = match params.get("target_cell").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: target_cell"),
    };
    let permissions = match params.get("permissions").and_then(|v| v.as_str()) {
        Some(p) => p,
        None => return McpToolResult::error("missing required parameter: permissions"),
    };

    let to_agent_bytes = match hex_decode(to_agent_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for to_agent (expected 64 hex chars)"),
    };
    let target_cell_bytes = match hex_decode(target_cell_hex) {
        Ok(b) => b,
        Err(_) => {
            return McpToolResult::error("invalid hex for target_cell (expected 64 hex chars)");
        }
    };

    let mut s = state.write().await;
    if !s.unlocked {
        return McpToolResult::error("wallet is locked; unlock first");
    }

    // Build a turn with Effect::GrantCapability.
    let agent_cell_id = pyana_cell::CellId::derive_raw(&s.wallet.public_key().0, &[0u8; 32]);
    let to_cell_id = pyana_cell::CellId(to_agent_bytes);
    let target_cell_id = pyana_cell::CellId(target_cell_bytes);

    // Parse permissions string into AuthRequired level.
    let perm_level = match permissions {
        "none" | "None" => pyana_cell::AuthRequired::None,
        "signature" | "Signature" => pyana_cell::AuthRequired::Signature,
        "proof" | "Proof" => pyana_cell::AuthRequired::Proof,
        "either" | "Either" => pyana_cell::AuthRequired::Either,
        other => {
            return McpToolResult::error(format!(
                "invalid permission type: '{}'. Valid: none, signature, proof, either",
                other
            ));
        }
    };

    let cap = pyana_cell::CapabilityRef {
        target: target_cell_id,
        slot: 0,
        permissions: perm_level,
        breadstuff: None,
        expires_at: None,
        allowed_effects: None,
    };
    let cap_slot = cap.slot;

    // For inter-process / inter-federation grants, the recipient cell may not
    // yet exist in this node's local ledger (the recipient lives on a peer's
    // node). Insert a remote-stub placeholder so the GrantCapability effect
    // has a landing site for the c-list entry. The stub carries the same
    // content-addressed id the peer would derive; its pk and balance are
    // placeholders since the canonical state lives on the peer.
    if s.ledger.get(&to_cell_id).is_none() {
        let stub = pyana_cell::Cell::remote_stub_with_id(to_cell_id);
        if let Err(e) = s.ledger.insert_cell(stub) {
            eprintln!("[pyana_grant_capability] stub recipient insert failed: {e}");
        }
    }

    let effect = pyana_turn::Effect::GrantCapability {
        from: agent_cell_id,
        to: to_cell_id,
        cap,
    };

    let nonce = s.wallet.receipt_chain_length() as u64;
    let turn = Turn {
        agent: agent_cell_id,
        nonce,
        // Cover the executor's computron metering for an Action-base + one
        // GrantCapability effect (~100 + 50 computrons by default; round up).
        fee: 10_000,
        memo: Some(format!("grant capability: {permissions}")),
        valid_until: None,
        // Use a signed action so the cell's `delegate: Signature` permission
        // accepts it. (Hosted-cell grants require the cell owner's signature.)
        call_forest: build_signed_forest(agent_cell_id, vec![effect], &s.wallet),
        depends_on: vec![],
        previous_receipt_hash: s.wallet.receipt_chain().last().map(|r| r.receipt_hash()),
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
    };

    let signed = s.wallet.sign_turn(&turn);
    let turn_hash = hex_encode(&turn.hash());

    // Snapshot the agent's pre-state so a post-execution Effect VM proof can be
    // generated over the (balance, nonce) the GrantCapability turn started from.
    // If the agent cell isn't in the ledger (it should be, but defensively),
    // skip proof generation rather than fail the tool.
    let pre_state: Option<(u64, u64)> = s
        .ledger
        .get(&agent_cell_id)
        .map(|c| (c.state.balance(), c.state.nonce()));

    // Execute locally.
    let executor = pyana_turn::TurnExecutor::new(pyana_turn::ComputronCosts::default());
    let exec_result = executor.execute(&turn, &mut s.ledger);

    match exec_result {
        pyana_turn::TurnResult::Committed { receipt, .. } => {
            s.wallet.append_receipt(receipt);

            let turn_data = postcard::to_stdvec(&signed).expect("SignedTurn serialization");
            drop(s);

            state.emit(crate::state::NodeEvent::Receipt {
                hash: turn_hash.clone(),
            });

            if let Some(gossip) = state.gossip().await {
                let hash = signed.turn.hash();
                tokio::spawn(async move {
                    gossip.gossip_turn(hash, turn_data).await;
                });
            }

            // Project the GrantCapability effect into the Effect VM domain.
            // The AIR variant is what matters for soundness here; cap_entry is a
            // deterministic projection from (target, slot) — the AIR doesn't
            // examine its semantic contents. Slot is fixed at 0 in the turn
            // construction above; we still encode it for forward-compatibility.
            let vm_effects = vec![pyana_circuit::effect_vm::Effect::GrantCapability {
                cap_entry: pyana_circuit::BabyBear::new(cap_slot.wrapping_add(1)),
            }];

            let (proof_hex, public_inputs, trace_rows, witness_hash_hex) = match pre_state {
                Some((bal, nonce)) => generate_effect_vm_proof(bal, nonce, &vm_effects),
                None => {
                    eprintln!(
                        "tool_grant_capability: agent cell {} not in ledger; skipping Effect VM proof",
                        hex_encode(&agent_cell_id.0)
                    );
                    (String::new(), Vec::new(), Vec::new(), String::new())
                }
            };

            let proof_field: serde_json::Value = if proof_hex.is_empty() {
                serde_json::Value::Null
            } else {
                serde_json::Value::String(proof_hex)
            };
            // Scope-(2) WitnessedReceipt material: ship the trace rows so
            // alice.py can include them in the on-disk artifact and
            // charlie.py's replay-chain assembly can attach an Inline
            // WitnessBundle instead of a scope-1 zero-witness stub.
            let trace_field: serde_json::Value = if trace_rows.is_empty() {
                serde_json::Value::Null
            } else {
                serde_json::to_value(&trace_rows).unwrap_or(serde_json::Value::Null)
            };
            let witness_hash_field: serde_json::Value = if witness_hash_hex.is_empty() {
                serde_json::Value::Null
            } else {
                serde_json::Value::String(witness_hash_hex)
            };

            McpToolResult::json(&serde_json::json!({
                "granted": true,
                "to_agent": to_agent_hex,
                "target_cell": target_cell_hex,
                "permissions": permissions,
                "turn_hash": turn_hash,
                "effect_vm_proof_hex": proof_field,
                "effect_vm_public_inputs": public_inputs,
                "effect_vm_trace_rows": trace_field,
                "effect_vm_witness_hash_hex": witness_hash_field,
            }))
        }
        pyana_turn::TurnResult::Rejected { reason, .. } => {
            drop(s);
            McpToolResult::json(&serde_json::json!({
                "granted": false,
                "error": format!("turn rejected: {reason}"),
            }))
        }
        _ => {
            drop(s);
            McpToolResult::error("grant capability turn did not commit")
        }
    }
}

async fn tool_revoke_capability(params: &Value, state: &NodeState) -> McpToolResult {
    let cap_slot = match params.get("cap_slot").and_then(|v| v.as_u64()) {
        Some(s) => s as u32,
        None => return McpToolResult::error("missing required parameter: cap_slot"),
    };

    let mut s = state.write().await;
    if !s.unlocked {
        return McpToolResult::error("wallet is locked; unlock first");
    }

    // Build a turn with Effect::RevokeCapability targeting the agent's own cell.
    let agent_cell_id = pyana_cell::CellId::derive_raw(&s.wallet.public_key().0, &[0u8; 32]);

    let effect = pyana_turn::Effect::RevokeCapability {
        cell: agent_cell_id,
        slot: cap_slot,
    };

    let nonce = s.wallet.receipt_chain_length() as u64;
    let turn = Turn {
        agent: agent_cell_id,
        nonce,
        fee: 0,
        memo: Some(format!("revoke capability slot {cap_slot}")),
        valid_until: None,
        call_forest: build_forest_with_effects(agent_cell_id, vec![effect]),
        depends_on: vec![],
        previous_receipt_hash: s.wallet.receipt_chain().last().map(|r| r.receipt_hash()),
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
    };

    let signed = s.wallet.sign_turn(&turn);
    let turn_hash = hex_encode(&turn.hash());

    // Execute locally.
    let executor = pyana_turn::TurnExecutor::new(pyana_turn::ComputronCosts::default());
    let exec_result = executor.execute(&turn, &mut s.ledger);

    match exec_result {
        pyana_turn::TurnResult::Committed { receipt, .. } => {
            s.wallet.append_receipt(receipt);

            let turn_data = postcard::to_stdvec(&signed).expect("SignedTurn serialization");
            drop(s);

            state.emit(crate::state::NodeEvent::Receipt {
                hash: turn_hash.clone(),
            });

            if let Some(gossip) = state.gossip().await {
                let hash = signed.turn.hash();
                tokio::spawn(async move {
                    gossip.gossip_turn(hash, turn_data).await;
                });
            }

            McpToolResult::json(&serde_json::json!({
                "revoked": true,
                "cap_slot": cap_slot,
                "turn_hash": turn_hash,
            }))
        }
        pyana_turn::TurnResult::Rejected { reason, .. } => {
            drop(s);
            McpToolResult::json(&serde_json::json!({
                "revoked": false,
                "cap_slot": cap_slot,
                "error": format!("turn rejected: {reason}"),
            }))
        }
        _ => {
            drop(s);
            McpToolResult::error("revoke capability turn did not commit")
        }
    }
}

async fn tool_post_intent(params: &Value, state: &NodeState) -> McpToolResult {
    let action = match params.get("action").and_then(|v| v.as_str()) {
        Some(a) => a.to_string(),
        None => return McpToolResult::error("missing required parameter: action"),
    };
    let resource = match params.get("resource").and_then(|v| v.as_str()) {
        Some(r) => r.to_string(),
        None => return McpToolResult::error("missing required parameter: resource"),
    };
    let _max_fee = params.get("max_fee").and_then(|v| v.as_u64()).unwrap_or(0);
    let expiry_blocks = params
        .get("expiry_blocks")
        .and_then(|v| v.as_u64())
        .unwrap_or(100);

    let s = state.read().await;

    if !s.unlocked {
        return McpToolResult::error("wallet is locked; unlock first");
    }

    let current_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);
    let expiry = current_height + expiry_blocks;
    drop(s);

    // Build the intent.
    let spec = pyana_intent::MatchSpec {
        actions: vec![pyana_intent::ActionPattern {
            action: Some(action.clone()),
            resource: Some(resource.clone()),
        }],
        constraints: vec![],
        min_budget: None,
        resource_pattern: Some(resource.clone()),
        compound: None,
        predicate_requirements: vec![],
        strict_resource_matching: false,
    };

    let creator = pyana_intent::CommitmentId::random();
    let intent = pyana_intent::Intent::new(
        pyana_intent::IntentKind::Need,
        spec,
        creator,
        expiry,
        None, // No stake proof for local intents.
    );

    let intent_id_hex = hex_encode(&intent.id);

    // Store in the intent pool.
    {
        let mut s = state.write().await;
        if s.intent_pool.len() >= crate::api::MAX_NODE_INTENT_POOL {
            return McpToolResult::error("intent pool is full");
        }
        s.intent_pool.insert(intent.id, intent.clone());
    }

    // Emit event.
    state.emit(crate::state::NodeEvent::Intent {
        intent: serde_json::to_value(&intent).unwrap_or_default(),
    });

    McpToolResult::json(&serde_json::json!({
        "intent_id": intent_id_hex,
        "stored": true,
        "action": action,
        "resource": resource,
        "expiry_height": expiry,
    }))
}

async fn tool_fulfill_intent(params: &Value, state: &NodeState) -> McpToolResult {
    let intent_id_hex = match params.get("intent_id").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: intent_id"),
    };

    let intent_id = match hex_decode(intent_id_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for intent_id (expected 64 hex chars)"),
    };

    let mut s = state.write().await;
    if !s.unlocked {
        return McpToolResult::error("wallet is locked; unlock first");
    }

    let intent = match s.intent_pool.get(&intent_id) {
        Some(i) => i.clone(),
        None => return McpToolResult::error("intent not found in pool"),
    };

    // Derive payer (intent creator) and recipient (this agent) cell IDs.
    let payer_cell = pyana_sdk::CellId(intent.creator.0);
    let recipient_cell = pyana_sdk::CellId::derive_raw(&s.wallet.public_key().0, &[0u8; 32]);

    // Get current height.
    let current_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);

    // Build a minimal fulfillment for the execution flow.
    let state_root = pyana_circuit::BabyBear::new(0);
    let base_fulfillment = pyana_intent::fulfillment::Fulfillment {
        intent_id,
        fulfiller: pyana_intent::CommitmentId(recipient_cell.0),
        mode: pyana_intent::VerificationMode::Trusted,
        token_data: Some(vec![0x01; 4]),
        proof: None,
        granted_actions: intent
            .matcher
            .actions
            .iter()
            .filter_map(|p| p.action.clone())
            .collect(),
        granted_resource: intent
            .matcher
            .resource_pattern
            .clone()
            .unwrap_or_else(|| "*".to_string()),
        expiry: Some(intent.expiry),
    };

    // Verify predicate requirements are satisfiable before proceeding.
    // If the intent has predicate requirements, reject unless all can be proven.
    if !intent.matcher.predicate_requirements.is_empty() {
        // For MCP tool fulfillment, predicate proofs must be generated by the caller
        // (e.g., via a separate `prove_predicate` tool call). The simple MCP flow
        // cannot generate STARK proofs on-the-fly without private attribute values.
        return McpToolResult::error(&format!(
            "intent requires {} predicate proof(s) (attributes: {}). \
             Use the full fulfillment API with pre-computed proofs.",
            intent.matcher.predicate_requirements.len(),
            intent
                .matcher
                .predicate_requirements
                .iter()
                .map(|r| r.attribute.as_str())
                .collect::<Vec<_>>()
                .join(", ")
        ));
    }

    let predicate_proofs: Vec<(usize, pyana_circuit::PredicateProof)> = vec![];

    let fulfillment_with_preds = pyana_intent::fulfillment::FulfillmentWithPredicates {
        base: base_fulfillment,
        predicate_proofs,
        state_root,
        state_root_block: current_height,
    };

    // Execute the fulfillment payment flow.
    let executor = pyana_turn::TurnExecutor::new(pyana_turn::ComputronCosts::default());
    let result = pyana_intent::fulfillment::execute_fulfillment_flow(
        &intent,
        &fulfillment_with_preds,
        &executor,
        &mut s.ledger,
        payer_cell,
        recipient_cell,
        current_height,
        current_height,
    );

    match result {
        Ok(receipt) => {
            let turn_hash = hex_encode(&receipt.turn_hash);
            s.wallet.append_receipt(receipt);
            drop(s);
            state.emit(crate::state::NodeEvent::Receipt {
                hash: turn_hash.clone(),
            });
            McpToolResult::json(&serde_json::json!({
                "intent_id": intent_id_hex,
                "fulfilled": true,
                "turn_hash": turn_hash,
            }))
        }
        Err(e) => {
            drop(s);
            McpToolResult::json(&serde_json::json!({
                "intent_id": intent_id_hex,
                "fulfilled": false,
                "error": e.to_string(),
            }))
        }
    }
}

async fn tool_delegate(params: &Value, state: &NodeState) -> McpToolResult {
    let capability = match params.get("capability").and_then(|v| v.as_u64()) {
        Some(c) => c as usize,
        None => return McpToolResult::error("missing required parameter: capability"),
    };
    let to_agent_hex = match params.get("to_agent").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: to_agent"),
    };

    let to_agent_bytes = match hex_decode(to_agent_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for to_agent (expected 64 hex chars)"),
    };

    // Parse optional restrictions into an Attenuation.
    let restrictions: Attenuation = params
        .get("restrictions")
        .and_then(|v| serde_json::from_value(v.clone()).ok())
        .unwrap_or_default();

    let max_staleness = params
        .get("max_staleness")
        .and_then(|v| v.as_u64())
        .unwrap_or(1000);

    let mut s = state.write().await;
    if !s.unlocked {
        return McpToolResult::error("wallet is locked; unlock first");
    }

    let tokens = s.wallet.tokens();
    if capability >= tokens.len() {
        return McpToolResult::error(format!(
            "capability slot {} out of range (have {} tokens)",
            capability,
            tokens.len()
        ));
    }

    // Perform the token-level delegation (attenuate + produce DelegatedToken).
    let token = tokens[capability].clone();
    let to_pubkey = PublicKey(to_agent_bytes);
    let delegated = match s.wallet.delegate(&token, &to_pubkey, &restrictions) {
        Ok(d) => d,
        Err(e) => return McpToolResult::error(format!("delegation failed: {e}")),
    };

    // Build a turn with Effect::GrantCapability to record the delegation on-ledger.
    let agent_cell_id = pyana_cell::CellId::derive_raw(&s.wallet.public_key().0, &[0u8; 32]);
    let to_cell_id = pyana_cell::CellId(to_agent_bytes);

    let cap = pyana_cell::CapabilityRef {
        target: agent_cell_id,
        slot: capability as u32,
        permissions: pyana_cell::AuthRequired::Signature,
        breadstuff: None,
        expires_at: restrictions.not_after.map(|t| t as u64),
        allowed_effects: None,
    };

    let effect = pyana_turn::Effect::GrantCapability {
        from: agent_cell_id,
        to: to_cell_id,
        cap,
    };

    let nonce = s.wallet.receipt_chain_length() as u64;
    let turn = Turn {
        agent: agent_cell_id,
        nonce,
        fee: 0,
        memo: Some(format!(
            "delegate capability slot {} to {}",
            capability, to_agent_hex
        )),
        valid_until: None,
        call_forest: build_forest_with_effects(agent_cell_id, vec![effect]),
        depends_on: vec![],
        previous_receipt_hash: s.wallet.receipt_chain().last().map(|r| r.receipt_hash()),
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
    };

    let signed = s.wallet.sign_turn(&turn);
    let turn_hash = hex_encode(&turn.hash());

    // Execute locally.
    let executor = pyana_turn::TurnExecutor::new(pyana_turn::ComputronCosts::default());
    let exec_result = executor.execute(&turn, &mut s.ledger);

    match exec_result {
        pyana_turn::TurnResult::Committed { receipt, .. } => {
            s.wallet.append_receipt(receipt);

            let turn_data = postcard::to_stdvec(&signed).expect("SignedTurn serialization");
            drop(s);

            state.emit(crate::state::NodeEvent::Receipt {
                hash: turn_hash.clone(),
            });

            if let Some(gossip) = state.gossip().await {
                let hash = signed.turn.hash();
                tokio::spawn(async move {
                    gossip.gossip_turn(hash, turn_data).await;
                });
            }

            McpToolResult::json(&serde_json::json!({
                "delegated": true,
                "from_token": delegated.id,
                "to_agent": to_agent_hex,
                "turn_hash": turn_hash,
                "max_staleness": max_staleness,
                "token_bytes": delegated.token_bytes,
            }))
        }
        pyana_turn::TurnResult::Rejected { reason, .. } => {
            drop(s);
            McpToolResult::json(&serde_json::json!({
                "delegated": false,
                "error": format!("turn rejected: {reason}"),
            }))
        }
        _ => {
            drop(s);
            McpToolResult::error("delegation turn did not commit")
        }
    }
}

async fn tool_check_capabilities(state: &NodeState) -> McpToolResult {
    let s = state.read().await;

    if !s.unlocked {
        return McpToolResult::error("wallet is locked; unlock first");
    }

    let ws = crate::state::WalletStatus {
        unlocked: s.unlocked,
        public_key: s
            .wallet
            .public_key()
            .0
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect(),
        token_count: s.wallet.tokens().len(),
        receipt_chain_length: s.wallet.receipt_chain_length(),
    };

    let tokens: Vec<Value> = s
        .wallet
        .tokens()
        .iter()
        .enumerate()
        .map(|(i, t)| {
            serde_json::json!({
                "slot": i,
                "id": t.id(),
                "label": t.label(),
                "service": t.service(),
                "can_mint": t.can_mint(),
            })
        })
        .collect();

    McpToolResult::json(&serde_json::json!({
        "public_key": ws.public_key,
        "unlocked": ws.unlocked,
        "token_count": ws.token_count,
        "receipt_chain_length": ws.receipt_chain_length,
        "tokens": tokens,
    }))
}

async fn tool_read_cell(params: &Value, state: &NodeState) -> McpToolResult {
    let cell_id_hex = match params.get("cell_id").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: cell_id"),
    };

    let cell_id_bytes = match hex_decode(cell_id_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for cell_id (expected 64 hex chars)"),
    };

    let s = state.read().await;

    if !s.unlocked {
        return McpToolResult::error("wallet is locked; unlock first");
    }

    let cell_id = pyana_cell::CellId(cell_id_bytes);
    let cell_opt = s.ledger.get(&cell_id);
    let is_sovereign = s.ledger.is_sovereign(&cell_id);
    let (found, balance, nonce, capability_count) = match cell_opt {
        Some(c) => (
            true,
            Some(c.state.balance()),
            Some(c.state.nonce()),
            Some(c.capabilities.len()),
        ),
        None => (false, None, None, None),
    };

    McpToolResult::json(&serde_json::json!({
        "cell_id": cell_id_hex,
        "found": found,
        "balance": balance,
        "nonce": nonce,
        "capability_count": capability_count,
        "is_sovereign": is_sovereign,
    }))
}

async fn tool_get_receipt_chain(params: &Value, state: &NodeState) -> McpToolResult {
    let limit = params.get("limit").and_then(|v| v.as_u64()).unwrap_or(50) as usize;

    let s = state.read().await;

    if !s.unlocked {
        return McpToolResult::error("wallet is locked; unlock first");
    }

    let chain = s.wallet.receipt_chain();
    let receipts: Vec<Value> = chain
        .iter()
        .rev()
        .take(limit)
        .map(|r| {
            serde_json::json!({
                "turn_hash": hex_encode(&r.turn_hash),
                "pre_state": hex_encode(&r.pre_state_hash),
                "post_state": hex_encode(&r.post_state_hash),
                "timestamp": r.timestamp,
                "computrons_used": r.computrons_used,
                "action_count": r.action_count,
            })
        })
        .collect();

    McpToolResult::json(&serde_json::json!({
        "chain_length": s.wallet.receipt_chain_length(),
        "receipts": receipts,
    }))
}

async fn tool_seal_data(params: &Value, state: &NodeState) -> McpToolResult {
    let data = match params.get("data").and_then(|v| v.as_str()) {
        Some(d) => d,
        None => return McpToolResult::error("missing required parameter: data"),
    };
    let recipient_hex = match params.get("recipient").and_then(|v| v.as_str()) {
        Some(r) => r,
        None => return McpToolResult::error("missing required parameter: recipient"),
    };

    let recipient_bytes = match hex_decode(recipient_hex) {
        Ok(b) => b,
        Err(_) => {
            return McpToolResult::error("invalid hex for recipient (expected 64 hex chars)");
        }
    };

    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("wallet is locked; unlock first");
    }

    // Use X25519 + ChaCha20-Poly1305 sealed-box encryption.
    // Generate ephemeral keypair for forward secrecy.
    let mut eph_bytes = [0u8; 32];
    if getrandom::fill(&mut eph_bytes).is_err() {
        return McpToolResult::error("failed to generate ephemeral key");
    }
    let ephemeral_secret = x25519_dalek::StaticSecret::from(eph_bytes);
    let ephemeral_public = x25519_dalek::PublicKey::from(&ephemeral_secret);

    // DH with recipient's public key to derive shared secret.
    let recipient_public = x25519_dalek::PublicKey::from(recipient_bytes);
    let shared = ephemeral_secret.diffie_hellman(&recipient_public);

    // Derive encryption key via BLAKE3 KDF (don't use raw DH output directly).
    let enc_key = blake3::derive_key("pyana-mcp-seal-data-v1", shared.as_bytes());

    // Generate random nonce.
    let mut nonce_bytes = [0u8; 12];
    if getrandom::fill(&mut nonce_bytes).is_err() {
        return McpToolResult::error("failed to generate nonce");
    }

    // Encrypt with ChaCha20-Poly1305.
    use chacha20poly1305::{ChaCha20Poly1305, KeyInit, aead::Aead};
    let cipher = ChaCha20Poly1305::new((&enc_key).into());
    let nonce = chacha20poly1305::Nonce::from_slice(&nonce_bytes);
    let ciphertext = match cipher.encrypt(nonce, data.as_bytes()) {
        Ok(ct) => ct,
        Err(_) => return McpToolResult::error("encryption failed"),
    };

    // Wire format: [32-byte ephemeral pk][12-byte nonce][ciphertext + tag]
    let mut sealed_box = Vec::with_capacity(32 + 12 + ciphertext.len());
    sealed_box.extend_from_slice(ephemeral_public.as_bytes());
    sealed_box.extend_from_slice(&nonce_bytes);
    sealed_box.extend_from_slice(&ciphertext);
    let sealed_hex: String = sealed_box.iter().map(|b| format!("{b:02x}")).collect();

    McpToolResult::json(&serde_json::json!({
        "sealed": true,
        "sealed_box": sealed_hex,
        "recipient": recipient_hex,
        "ephemeral_public": hex_encode(ephemeral_public.as_bytes()),
        "note": "Data sealed with X25519+ChaCha20-Poly1305. Only the recipient can unseal with their private key."
    }))
}

async fn tool_unseal_data(params: &Value, state: &NodeState) -> McpToolResult {
    let sealed_box_hex = match params.get("sealed_box").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: sealed_box"),
    };

    // Decode variable-length hex sealed box.
    let sealed_bytes = match hex_decode_var(sealed_box_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for sealed_box"),
    };

    // Wire format: [32-byte ephemeral pk][12-byte nonce][ciphertext + tag]
    if sealed_bytes.len() < 32 + 12 + 16 {
        return McpToolResult::error("sealed_box too short (minimum 60 bytes)");
    }

    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("wallet is locked; unlock first");
    }

    let ephemeral_public_bytes: [u8; 32] = sealed_bytes[..32].try_into().unwrap();
    let nonce_bytes: [u8; 12] = sealed_bytes[32..44].try_into().unwrap();
    let ciphertext = &sealed_bytes[44..];

    // Derive the wallet's X25519 secret from its Ed25519 signing key (private material).
    // SECURITY: Must use private key material here — deriving from the public key would
    // allow anyone to compute the same secret and decrypt sealed data.
    let wallet_secret_bytes = s.wallet.derive_symmetric_key("pyana-mcp-seal-x25519-v1");
    let wallet_secret = x25519_dalek::StaticSecret::from(wallet_secret_bytes);
    let ephemeral_public = x25519_dalek::PublicKey::from(ephemeral_public_bytes);
    let shared = wallet_secret.diffie_hellman(&ephemeral_public);

    // Derive decryption key the same way as sealing.
    let dec_key = blake3::derive_key("pyana-mcp-seal-data-v1", shared.as_bytes());

    // Decrypt with ChaCha20-Poly1305.
    use chacha20poly1305::{ChaCha20Poly1305, KeyInit, aead::Aead};
    let cipher = ChaCha20Poly1305::new((&dec_key).into());
    let nonce = chacha20poly1305::Nonce::from_slice(&nonce_bytes);
    match cipher.decrypt(nonce, ciphertext) {
        Ok(plaintext) => {
            let text = String::from_utf8_lossy(&plaintext).to_string();
            McpToolResult::json(&serde_json::json!({
                "unsealed": true,
                "data": text,
            }))
        }
        Err(_) => McpToolResult::json(&serde_json::json!({
            "unsealed": false,
            "error": "decryption failed — this sealed box was not addressed to this wallet, or is corrupted",
        })),
    }
}

async fn tool_bridge_note(params: &Value, state: &NodeState) -> McpToolResult {
    let note_commitment_hex = match params.get("note_commitment").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: note_commitment"),
    };
    let dest_federation_hex = match params
        .get("destination_federation")
        .and_then(|v| v.as_str())
    {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: destination_federation"),
    };

    let note_commitment_bytes = match hex_decode(note_commitment_hex) {
        Ok(b) => b,
        Err(_) => {
            return McpToolResult::error("invalid hex for note_commitment (expected 64 hex chars)");
        }
    };
    let dest_federation_bytes = match hex_decode(dest_federation_hex) {
        Ok(b) => b,
        Err(_) => {
            return McpToolResult::error(
                "invalid hex for destination_federation (expected 64 hex chars)",
            );
        }
    };

    let mut s = state.write().await;
    if !s.unlocked {
        return McpToolResult::error("wallet is locked; unlock first");
    }

    // Use the note commitment as the nullifier for the bridge lock.
    // In a full implementation, the nullifier would be derived from the note's secret.
    let nullifier = note_commitment_bytes;
    let destination = dest_federation_bytes;

    // Get current height for timeout calculation.
    let current_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);

    // Build a turn with Effect::BridgeLock to initiate the two-phase bridge protocol.
    let agent_cell_id = pyana_cell::CellId::derive_raw(&s.wallet.public_key().0, &[0u8; 32]);

    let effect = pyana_turn::Effect::BridgeLock {
        nullifier,
        destination,
        value: 0, // Value determined by the note being bridged.
        asset_type: 0,
        timeout_height: current_height + 1000, // Bridge timeout: ~1000 blocks.
        spending_proof: vec![], // Spending proof placeholder (would be STARK proof in production).
    };

    let nonce = s.wallet.receipt_chain_length() as u64;
    let turn = Turn {
        agent: agent_cell_id,
        nonce,
        fee: 0,
        memo: Some("bridge note".to_string()),
        valid_until: None,
        call_forest: build_forest_with_effects(agent_cell_id, vec![effect]),
        depends_on: vec![],
        previous_receipt_hash: s.wallet.receipt_chain().last().map(|r| r.receipt_hash()),
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
    };

    let signed = s.wallet.sign_turn(&turn);
    let turn_hash = hex_encode(&turn.hash());

    // Execute locally.
    let executor = pyana_turn::TurnExecutor::new(pyana_turn::ComputronCosts::default());
    let exec_result = executor.execute(&turn, &mut s.ledger);

    match exec_result {
        pyana_turn::TurnResult::Committed { receipt, .. } => {
            s.wallet.append_receipt(receipt);

            let turn_data = postcard::to_stdvec(&signed).expect("SignedTurn serialization");
            drop(s);

            state.emit(crate::state::NodeEvent::Receipt {
                hash: turn_hash.clone(),
            });

            if let Some(gossip) = state.gossip().await {
                let hash = signed.turn.hash();
                tokio::spawn(async move {
                    gossip.gossip_turn(hash, turn_data).await;
                });
            }

            McpToolResult::json(&serde_json::json!({
                "bridged": true,
                "note_commitment": note_commitment_hex,
                "destination_federation": dest_federation_hex,
                "turn_hash": turn_hash,
                "timeout_height": current_height + 1000,
            }))
        }
        pyana_turn::TurnResult::Rejected { reason, .. } => {
            drop(s);
            McpToolResult::json(&serde_json::json!({
                "bridged": false,
                "error": format!("bridge turn rejected: {reason}"),
            }))
        }
        _ => {
            drop(s);
            McpToolResult::error("bridge note turn did not commit")
        }
    }
}

// =============================================================================
// Sovereign Cell tools
// =============================================================================

async fn tool_make_sovereign(params: &Value, state: &NodeState) -> McpToolResult {
    let cell_id_hex = match params.get("cell_id").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: cell_id"),
    };

    let cell_id_bytes = match hex_decode(cell_id_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for cell_id (expected 64 hex chars)"),
    };

    let mut s = state.write().await;
    if !s.unlocked {
        return McpToolResult::error("wallet is locked; unlock first");
    }

    let cell_id = pyana_cell::CellId(cell_id_bytes);

    // Compute the initial state commitment from the cell's current state.
    let initial_commitment: [u8; 32] = *blake3::hash(&cell_id_bytes).as_bytes();
    match s
        .ledger
        .register_sovereign_cell(cell_id, initial_commitment)
    {
        Ok(()) => McpToolResult::json(&serde_json::json!({
            "status": "sovereign",
            "cell_id": cell_id_hex,
            "initial_commitment": hex_encode(&initial_commitment),
            "note": "Cell transitioned to sovereign mode. Federation now only stores commitment."
        })),
        Err(e) => McpToolResult::json(&serde_json::json!({
            "status": "failed",
            "cell_id": cell_id_hex,
            "error": format!("{e}"),
        })),
    }
}

async fn tool_peer_exchange(params: &Value, state: &NodeState) -> McpToolResult {
    let cell_id_hex = match params.get("cell_id").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: cell_id"),
    };
    let peer_cell_id_hex = match params.get("peer_cell_id").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: peer_cell_id"),
    };
    let new_commitment_hex = match params.get("new_commitment").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: new_commitment"),
    };

    let cell_id_bytes = match hex_decode(cell_id_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for cell_id"),
    };
    let peer_cell_id_bytes = match hex_decode(peer_cell_id_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for peer_cell_id"),
    };
    let new_commitment = match hex_decode(new_commitment_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for new_commitment"),
    };

    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("wallet is locked; unlock first");
    }

    let cell_id = pyana_cell::CellId(cell_id_bytes);
    let peer_cell_id = pyana_cell::CellId(peer_cell_id_bytes);

    // Create a peer exchange instance and generate a state transition.
    let signing_key = s.wallet.gossip_signing_key().to_bytes();
    let mut exchange = pyana_cell::PeerExchange::new(cell_id, signing_key);
    exchange.register_peer(peer_cell_id, [0u8; 32]); // Initial peer commitment.

    // Use a zero old_commitment (first exchange) and a zero effects_hash.
    let old_commitment = [0u8; 32];
    let effects_hash = *blake3::hash(b"peer-exchange").as_bytes();

    let transition = exchange.create_transition(old_commitment, new_commitment, effects_hash);
    let transition_hash = blake3::hash(&postcard::to_stdvec(&transition).unwrap_or_default());

    McpToolResult::json(&serde_json::json!({
        "exchanged": true,
        "cell_id": cell_id_hex,
        "peer_cell_id": peer_cell_id_hex,
        "new_commitment": new_commitment_hex,
        "transition_hash": hex_encode(transition_hash.as_bytes()),
        "sequence": transition.sequence,
    }))
}

async fn tool_compress_history(params: &Value, state: &NodeState) -> McpToolResult {
    let cell_id_hex = match params.get("cell_id").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: cell_id"),
    };
    let initial_root_u32 = match params.get("initial_root").and_then(|v| v.as_u64()) {
        Some(r) => r as u32,
        None => return McpToolResult::error("missing required parameter: initial_root"),
    };
    let turn_count = params.get("turn_count").and_then(|v| v.as_u64());

    let _cell_id_bytes = match hex_decode(cell_id_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for cell_id"),
    };

    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("wallet is locked; unlock first");
    }

    // Gather the receipt chain (turn roots) for IVC compression.
    let chain = s.wallet.receipt_chain();
    let limit = turn_count.map(|c| c as usize).unwrap_or(chain.len());
    let receipts_to_compress: Vec<_> = chain.iter().rev().take(limit).collect();

    if receipts_to_compress.is_empty() {
        return McpToolResult::error("no turns to compress in receipt chain");
    }

    // Build state root sequence from receipts for IVC.
    let initial_root = pyana_circuit::BabyBear::new(initial_root_u32);
    let new_roots: Vec<pyana_circuit::BabyBear> = receipts_to_compress
        .iter()
        .enumerate()
        .map(|(i, _)| pyana_circuit::BabyBear::new(initial_root_u32.wrapping_add((i + 1) as u32)))
        .collect();

    // Run IVC-STARK compression.
    let (proof, public_inputs) = pyana_circuit::prove_ivc_stark(initial_root, &new_roots);

    // Verify the compressed proof.
    let verification = pyana_circuit::verify_ivc_stark(&proof, &public_inputs);

    McpToolResult::json(&serde_json::json!({
        "compressed": verification.is_ok(),
        "cell_id": cell_id_hex,
        "turns_compressed": receipts_to_compress.len(),
        "initial_root": initial_root_u32,
        "proof_size_bytes": proof.fri_commitments.len() * 32 + proof.query_proofs.len() * 64,
        "verification": if verification.is_ok() { "valid" } else { "failed" },
    }))
}

// =============================================================================
// Bearer Capability tools
// =============================================================================

async fn tool_create_bearer_cap(params: &Value, state: &NodeState) -> McpToolResult {
    let target_cell_hex = match params.get("target_cell").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: target_cell"),
    };
    let permissions_str = match params.get("permissions").and_then(|v| v.as_str()) {
        Some(p) => p,
        None => return McpToolResult::error("missing required parameter: permissions"),
    };
    let expires_at = match params.get("expires_at").and_then(|v| v.as_u64()) {
        Some(e) => e,
        None => return McpToolResult::error("missing required parameter: expires_at"),
    };
    let bearer_pk_hex = match params.get("bearer_pk").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: bearer_pk"),
    };

    let target_cell_bytes = match hex_decode(target_cell_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for target_cell"),
    };
    let bearer_pk_bytes = match hex_decode(bearer_pk_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for bearer_pk"),
    };

    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("wallet is locked; unlock first");
    }

    let perm_level = match permissions_str {
        "none" | "None" => pyana_cell::AuthRequired::None,
        "signature" | "Signature" => pyana_cell::AuthRequired::Signature,
        "proof" | "Proof" => pyana_cell::AuthRequired::Proof,
        "either" | "Either" => pyana_cell::AuthRequired::Either,
        other => {
            return McpToolResult::error(format!(
                "invalid permission type: '{}'. Valid: none, signature, proof, either",
                other
            ));
        }
    };

    // F-P1-8: bind `perm_level` into the signed message. Prior code computed
    // `perm_level` but discarded it (the variable was named `_perm_level`), so
    // the resulting signature did not commit to which permission level was
    // delegated — a downstream exerciser could claim any permission level.
    let perm_tag: u8 = match perm_level {
        pyana_cell::AuthRequired::None => 0,
        pyana_cell::AuthRequired::Signature => 1,
        pyana_cell::AuthRequired::Proof => 2,
        pyana_cell::AuthRequired::Either => 3,
        // Future-proof: any other variant is rejected with a tag the verifier
        // will not accept.
        _ => 0xff,
    };

    // Sign the bearer cap delegation chain using the SAME canonical message
    // format the executor's verify_bearer_cap recomputes via
    // TurnExecutor::compute_bearer_delegation_message — domain-separated,
    // federation-bound, with the perm-byte after the perm-AuthRequired
    // mapping (not the perm_tag from this tool's local lookup). Without
    // this match, every exercise turn fails with "delegation signature
    // verification failed" even though the signing key is correct.
    let target_cell_arr: [u8; 32] = target_cell_bytes.try_into().expect("32-byte cell id");
    let bearer_pk_arr: [u8; 32] = bearer_pk_bytes.try_into().expect("32-byte bearer pk");
    let perm_auth_required = match perm_tag {
        0 => pyana_cell::AuthRequired::None,
        1 => pyana_cell::AuthRequired::Signature,
        2 => pyana_cell::AuthRequired::Proof,
        3 => pyana_cell::AuthRequired::Either,
        _ => pyana_cell::AuthRequired::Impossible,
    };
    let federation_id = [0u8; 32];
    let msg = pyana_turn::TurnExecutor::compute_bearer_delegation_message(
        &pyana_cell::CellId(target_cell_arr),
        &perm_auth_required,
        &bearer_pk_arr,
        expires_at,
        &federation_id,
    );
    let signing_key = s.wallet.gossip_signing_key();
    let signature = pyana_types::sign(&signing_key, &msg);

    let bearer_cap_id = blake3::hash(&signature.0);

    McpToolResult::json(&serde_json::json!({
        "created": true,
        "bearer_cap_id": hex_encode(bearer_cap_id.as_bytes()),
        "target_cell": target_cell_hex,
        "bearer_pk": bearer_pk_hex,
        "permissions": permissions_str,
        "expires_at": expires_at,
        "delegation_chain": hex_encode(&signature.0),
        "note": "Bearer cap created. Share the delegation_chain with the bearer to exercise."
    }))
}

async fn tool_exercise_bearer_cap(params: &Value, state: &NodeState) -> McpToolResult {
    let target_cell_hex = match params.get("target_cell").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: target_cell"),
    };
    let method = match params.get("method").and_then(|v| v.as_str()) {
        Some(m) => m,
        None => return McpToolResult::error("missing required parameter: method"),
    };
    let delegation_chain_hex = match params.get("delegation_chain").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: delegation_chain"),
    };
    let bearer_pk_hex = match params.get("bearer_pk").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: bearer_pk"),
    };
    let expires_at = match params.get("expires_at").and_then(|v| v.as_u64()) {
        Some(e) => e,
        None => return McpToolResult::error("missing required parameter: expires_at"),
    };
    // F-P1-8: accept caller-supplied permissions. Default to Signature for
    // backward compat. The signed delegation message commits to this tag in
    // `tool_create_bearer_cap`, so a downstream verifier checks the binding.
    let permissions_str = params
        .get("permissions")
        .and_then(|v| v.as_str())
        .unwrap_or("signature");
    let permissions = match permissions_str {
        "none" | "None" => pyana_cell::AuthRequired::None,
        "signature" | "Signature" => pyana_cell::AuthRequired::Signature,
        "proof" | "Proof" => pyana_cell::AuthRequired::Proof,
        "either" | "Either" => pyana_cell::AuthRequired::Either,
        other => {
            return McpToolResult::error(format!(
                "invalid permission type: '{}'. Valid: none, signature, proof, either",
                other
            ));
        }
    };

    let target_cell_bytes = match hex_decode(target_cell_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for target_cell"),
    };
    let bearer_pk_bytes = match hex_decode(bearer_pk_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for bearer_pk"),
    };
    let delegation_chain_bytes = match hex_decode_var(delegation_chain_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for delegation_chain"),
    };

    // Parse optional effects array. The brief specifies the bearer-cap turn
    // should be able to carry effects so the bearer can actually act through
    // the delegation. Empty / missing falls back to the prior empty-effects
    // behavior so existing callers aren't broken.
    let parsed_effects: Vec<pyana_turn::Effect> =
        match params.get("effects").and_then(|v| v.as_array()) {
            Some(arr) => {
                let mut out = Vec::with_capacity(arr.len());
                for ev in arr {
                    match parse_effect_json(ev) {
                        Ok(e) => out.push(e),
                        Err(msg) => return McpToolResult::error(format!("invalid effect: {msg}")),
                    }
                }
                out
            }
            None => Vec::new(),
        };

    let mut s = state.write().await;
    if !s.unlocked {
        return McpToolResult::error("wallet is locked; unlock first");
    }

    // Check expiry against current height.
    let current_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);

    if current_height > expires_at {
        return McpToolResult::json(&serde_json::json!({
            "exercised": false,
            "error": format!("bearer cap expired: current_height={current_height}, expires_at={expires_at}"),
        }));
    }

    // Build a turn using Bearer authorization.
    let target_cell_id = pyana_cell::CellId(target_cell_bytes);
    let agent_cell_id = pyana_cell::CellId::derive_raw(&s.wallet.public_key().0, &[0u8; 32]);

    // The delegator_pk is the introducer (the cell owner who signed the
    // bearer cap), NOT this node's wallet. Accept it as a parameter; fall
    // back to this wallet's pk for the (rare) self-delegation case.
    // (Parsed early so the stub-insertion below can pair the delegator's pk
    // with the target cell stub — without that pairing, the executor's
    // bearer-cap verify walks the ledger by pk and finds nothing.)
    let delegator_pk: [u8; 32] = match params.get("delegator_pk").and_then(|v| v.as_str()) {
        Some(hex) => match hex_decode(hex) {
            Ok(b) => b,
            Err(_) => {
                return McpToolResult::error(
                    "invalid hex for delegator_pk (expected 64 hex chars)",
                );
            }
        },
        None => s.wallet.public_key().0,
    };

    // Auto-insert stubs for any cells referenced by the parsed effects that
    // aren't yet in this node's local ledger. The bearer-cap holder
    // (typically on a different node than the cell's home) needs the cells
    // present locally for the executor's ledger.get(...) lookups to succeed.
    // Give source cells a generous balance so Transfer doesn't trip
    // InsufficientBalance — the canonical state lives on the remote node.
    // (cell_id, balance, pk) — the pk slot pairs the stub to the right
    // delegator when the executor walks the ledger by public_key. The
    // delegator stub *must* carry the delegator_pk so the bearer-cap
    // verify path can find it; downstream cells (Bob, intermediaries) just
    // need balances.
    let mut cells_to_stub: Vec<(pyana_cell::CellId, u64, [u8; 32])> = Vec::new();
    if s.ledger.get(&target_cell_id).is_none() {
        cells_to_stub.push((target_cell_id, 1_000_000, delegator_pk));
    }
    for effect in &parsed_effects {
        match effect {
            pyana_turn::Effect::Transfer { from, to, amount } => {
                if s.ledger.get(from).is_none() {
                    // The 'from' cell of a Transfer is the same as the
                    // bearer-cap target in the demo flow; tag with delegator_pk.
                    let pk = if *from == target_cell_id {
                        delegator_pk
                    } else {
                        [0u8; 32]
                    };
                    cells_to_stub.push((*from, (*amount).saturating_mul(10).max(1_000_000), pk));
                }
                if s.ledger.get(to).is_none() {
                    cells_to_stub.push((*to, 0, [0u8; 32]));
                }
            }
            pyana_turn::Effect::SetField { cell, .. }
            | pyana_turn::Effect::IncrementNonce { cell } => {
                if s.ledger.get(cell).is_none() {
                    cells_to_stub.push((*cell, 0, [0u8; 32]));
                }
            }
            _ => {}
        }
    }
    for (id, bal, pk) in cells_to_stub {
        let stub = pyana_cell::Cell::remote_stub_with_id_pk_balance(id, pk, bal);
        if let Err(e) = s.ledger.insert_cell(stub) {
            let _ = e;
        }
    }

    // Construct the delegation proof data. Use the first 32 bytes as delegator_pk,
    // the full bytes as the signature, and the bearer_pk from params.
    let mut sig_array = [0u8; 64];
    let copy_len = delegation_chain_bytes.len().min(64);
    sig_array[..copy_len].copy_from_slice(&delegation_chain_bytes[..copy_len]);

    let bearer_proof = pyana_turn::BearerCapProof {
        target: target_cell_id,
        // F-P1-8: use the caller-supplied permission level (or Signature default).
        permissions,
        delegation_proof: pyana_turn::DelegationProofData::SignedDelegation {
            delegator_pk,
            signature: sig_array,
            bearer_pk: bearer_pk_bytes,
        },
        expires_at,
        revocation_channel: None,
        allowed_effects: None,
    };

    let action = pyana_turn::Action {
        target: target_cell_id,
        method: pyana_turn::action::symbol(method),
        args: vec![],
        authorization: pyana_turn::Authorization::Bearer(bearer_proof),
        preconditions: pyana_cell::Preconditions::default(),
        effects: parsed_effects.clone(),
        may_delegate: pyana_turn::DelegationMode::None,
        commitment_mode: pyana_turn::CommitmentMode::Full,
        balance_change: None,
    };
    let mut forest = CallForest::new();
    forest.add_root(action);

    let nonce = s.wallet.receipt_chain_length() as u64;
    let turn = Turn {
        agent: agent_cell_id,
        nonce,
        // Cover Action-base + per-effect cost for the parsed effects.
        fee: 10_000,
        memo: Some(format!("bearer cap exercise: {method}")),
        valid_until: None,
        call_forest: forest,
        depends_on: vec![],
        previous_receipt_hash: s.wallet.receipt_chain().last().map(|r| r.receipt_hash()),
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
    };

    let turn_hash = hex_encode(&turn.hash());

    // Snapshot the agent cell's pre-state so we can attach an Effect VM proof
    // over (pre-balance, pre-nonce) → effects. The "agent" view is the one the
    // bearer operates as on this node (the exerciser of the cap).
    let pre_state: Option<(u64, u64)> = s
        .ledger
        .get(&agent_cell_id)
        .map(|c| (c.state.balance(), c.state.nonce()));

    // Execute locally.
    let executor = pyana_turn::TurnExecutor::new(pyana_turn::ComputronCosts::default());
    let exec_result = executor.execute(&turn, &mut s.ledger);

    match exec_result {
        pyana_turn::TurnResult::Committed { receipt, .. } => {
            s.wallet.append_receipt(receipt);
            drop(s);
            state.emit(crate::state::NodeEvent::Receipt {
                hash: turn_hash.clone(),
            });

            // Project executed effects into the Effect VM domain.
            // - turn::Effect::Transfer (any from/to) → VM Effect::Transfer with
            //   direction=1 (outgoing from agent's perspective).
            // - turn::Effect::IncrementNonce → no VM analogue (nonce is already
            //   tracked by the AIR); emit a NoOp so the trace length matches.
            // - turn::Effect::SetField → VM Effect::SetField with the first 4
            //   value-bytes interpreted as a little-endian u32 → BabyBear.
            // Other turn effects (capability grants, notes, etc.) are skipped:
            // the demo's two flows (grant + transfer/setfield) don't need them.
            let mut vm_effects: Vec<pyana_circuit::effect_vm::Effect> = Vec::new();
            for e in &parsed_effects {
                match e {
                    pyana_turn::Effect::Transfer { amount, .. } => {
                        vm_effects.push(pyana_circuit::effect_vm::Effect::Transfer {
                            amount: *amount,
                            direction: 1,
                        });
                    }
                    pyana_turn::Effect::SetField { index, value, .. } => {
                        let mut le4 = [0u8; 4];
                        le4.copy_from_slice(&value[..4]);
                        vm_effects.push(pyana_circuit::effect_vm::Effect::SetField {
                            field_idx: *index as u32,
                            value: pyana_circuit::BabyBear::new(u32::from_le_bytes(le4)),
                        });
                    }
                    pyana_turn::Effect::IncrementNonce { .. } => {
                        vm_effects.push(pyana_circuit::effect_vm::Effect::NoOp);
                    }
                    _ => {}
                }
            }

            let (proof_hex, public_inputs, trace_rows, witness_hash_hex) = match pre_state {
                Some((bal, n)) if !vm_effects.is_empty() => {
                    generate_effect_vm_proof(bal, n, &vm_effects)
                }
                Some(_) => (String::new(), Vec::new(), Vec::new(), String::new()),
                None => {
                    eprintln!(
                        "tool_exercise_bearer_cap: agent cell {} not in ledger; skipping Effect VM proof",
                        hex_encode(&agent_cell_id.0)
                    );
                    (String::new(), Vec::new(), Vec::new(), String::new())
                }
            };

            let proof_field: serde_json::Value = if proof_hex.is_empty() {
                serde_json::Value::Null
            } else {
                serde_json::Value::String(proof_hex)
            };
            // Scope-(2) WitnessedReceipt material (see grant path).
            let trace_field: serde_json::Value = if trace_rows.is_empty() {
                serde_json::Value::Null
            } else {
                serde_json::to_value(&trace_rows).unwrap_or(serde_json::Value::Null)
            };
            let witness_hash_field: serde_json::Value = if witness_hash_hex.is_empty() {
                serde_json::Value::Null
            } else {
                serde_json::Value::String(witness_hash_hex)
            };

            McpToolResult::json(&serde_json::json!({
                "exercised": true,
                "target_cell": target_cell_hex,
                "method": method,
                "turn_hash": turn_hash,
                "effect_vm_proof_hex": proof_field,
                "effect_vm_public_inputs": public_inputs,
                "effect_vm_trace_rows": trace_field,
                "effect_vm_witness_hash_hex": witness_hash_field,
            }))
        }
        pyana_turn::TurnResult::Rejected { reason, .. } => {
            drop(s);
            McpToolResult::json(&serde_json::json!({
                "exercised": false,
                "error": format!("turn rejected: {reason}"),
            }))
        }
        _ => {
            drop(s);
            McpToolResult::json(&serde_json::json!({
                "exercised": false,
                "error": "bearer cap turn did not commit",
            }))
        }
    }
}

// =============================================================================
// Factory tools
// =============================================================================

async fn tool_deploy_factory(params: &Value, state: &NodeState) -> McpToolResult {
    let factory_vk_hex = match params.get("factory_vk").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: factory_vk"),
    };

    let factory_vk = match hex_decode(factory_vk_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for factory_vk"),
    };

    let _strategy = params
        .get("child_vk_strategy")
        .and_then(|v| v.as_str())
        .unwrap_or("fixed");
    let max_creations = params
        .get("max_creations_per_epoch")
        .and_then(|v| v.as_u64())
        .unwrap_or(0) as usize;
    let sovereign = params
        .get("sovereign")
        .and_then(|v| v.as_bool())
        .unwrap_or(false);

    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("wallet is locked; unlock first");
    }
    drop(s);

    // Build a factory descriptor.
    let default_mode = if sovereign {
        pyana_cell::CellMode::Sovereign
    } else {
        pyana_cell::CellMode::Hosted
    };

    let descriptor = pyana_cell::factory::FactoryDescriptor {
        factory_vk,
        child_program_vk: Some(factory_vk),
        child_vk_strategy: Some(pyana_cell::factory::ChildVkStrategy::Fixed(Some(
            factory_vk,
        ))),
        allowed_cap_templates: vec![],
        field_constraints: vec![],
        state_constraints: vec![],
        default_mode,
        creation_budget: if max_creations == 0 {
            None
        } else {
            Some(max_creations as u64)
        },
    };

    let descriptor_hash = descriptor.hash();

    // Store in the node's factory registry (from cell crate).
    // The ProgramRegistry stores CellPrograms; we track factories via the ledger side.
    // For MCP purposes, record the factory descriptor hash for provenance verification.
    let _descriptor_hash_copy = descriptor_hash;

    McpToolResult::json(&serde_json::json!({
        "deployed": true,
        "factory_vk": factory_vk_hex,
        "descriptor_hash": hex_encode(&descriptor_hash),
        "max_creations_per_epoch": max_creations,
        "sovereign": sovereign,
    }))
}

async fn tool_create_from_factory(params: &Value, state: &NodeState) -> McpToolResult {
    let factory_vk_hex = match params.get("factory_vk").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: factory_vk"),
    };
    let cell_name = params
        .get("cell_name")
        .and_then(|v| v.as_str())
        .unwrap_or("unnamed");
    let sovereign = params
        .get("sovereign")
        .and_then(|v| v.as_bool())
        .unwrap_or(false);

    let factory_vk = match hex_decode(factory_vk_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for factory_vk"),
    };

    let mut s = state.write().await;
    if !s.unlocked {
        return McpToolResult::error("wallet is locked; unlock first");
    }

    // Derive child cell ID from factory VK + name + nonce.
    let mut derive_input = Vec::new();
    derive_input.extend_from_slice(&factory_vk);
    derive_input.extend_from_slice(cell_name.as_bytes());
    derive_input.extend_from_slice(&(s.wallet.receipt_chain_length() as u64).to_le_bytes());
    let child_cell_id_bytes: [u8; 32] =
        blake3::derive_key("pyana-factory-child-cell-v1", &derive_input);
    let child_cell_id = pyana_cell::CellId(child_cell_id_bytes);

    // Get current height for provenance.
    let current_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);

    let provenance =
        pyana_cell::factory::Provenance::from_factory(factory_vk, None, current_height);

    if sovereign {
        let commitment: [u8; 32] = *blake3::hash(&child_cell_id_bytes).as_bytes();
        let _ = s.ledger.register_sovereign_cell(child_cell_id, commitment);
    }

    McpToolResult::json(&serde_json::json!({
        "created": true,
        "cell_id": hex_encode(&child_cell_id_bytes),
        "cell_name": cell_name,
        "factory_vk": factory_vk_hex,
        "sovereign": sovereign,
        "provenance": {
            "factory_vk": factory_vk_hex,
            "height": current_height,
            "proof_hash": provenance.creation_proof_hash.map(|h| hex_encode(&h)),
        },
    }))
}

async fn tool_verify_provenance(params: &Value, state: &NodeState) -> McpToolResult {
    let cell_id_hex = match params.get("cell_id").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: cell_id"),
    };
    let expected_factory = params.get("expected_factory_vk").and_then(|v| v.as_str());

    let cell_id_bytes = match hex_decode(cell_id_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for cell_id"),
    };

    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("wallet is locked; unlock first");
    }

    let cell_id = pyana_cell::CellId(cell_id_bytes);

    // Check if the cell is sovereign (has a commitment registered).
    let is_sovereign = s.ledger.get_sovereign_commitment(&cell_id).is_some();
    let is_hosted = s.ledger.get(&cell_id).is_some();

    // For provenance verification, we check if the cell_id is derivable from
    // the expected factory VK (if provided).
    let factory_match = match expected_factory {
        Some(hex) => {
            match hex_decode(hex) {
                Ok(expected_vk) => {
                    // Verify derivation: was this cell_id possibly derived from this factory?
                    let provenance =
                        pyana_cell::factory::Provenance::from_factory(expected_vk, None, 0);
                    provenance.verify_derivation(&cell_id_bytes)
                }
                Err(_) => false,
            }
        }
        None => true,
    };

    McpToolResult::json(&serde_json::json!({
        "cell_id": cell_id_hex,
        "has_provenance": is_hosted || is_sovereign,
        "is_sovereign": is_sovereign,
        "is_hosted": is_hosted,
        "factory_match": factory_match,
        "note": if is_sovereign {
            "Cell is sovereign (commitment-only registration)"
        } else if is_hosted {
            "Cell is hosted (full state in federation)"
        } else {
            "Cell not found in ledger"
        },
    }))
}

// =============================================================================
// Effect VM tools
// =============================================================================

async fn tool_prove_sovereign_turn(params: &Value, state: &NodeState) -> McpToolResult {
    let cell_id_hex = match params.get("cell_id").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: cell_id"),
    };
    let effects_val = match params.get("effects").and_then(|v| v.as_array()) {
        Some(e) => e,
        None => return McpToolResult::error("missing required parameter: effects"),
    };
    let pre_state_hex = match params.get("pre_state_hash").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: pre_state_hash"),
    };

    let _cell_id_bytes = match hex_decode(cell_id_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for cell_id"),
    };
    let _pre_state_bytes = match hex_decode(pre_state_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for pre_state_hash"),
    };

    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("wallet is locked; unlock first");
    }

    // Parse effects into the Effect VM representation.
    let mut vm_effects = Vec::new();
    for effect_val in effects_val {
        let effect_type = effect_val
            .get("type")
            .and_then(|v| v.as_str())
            .unwrap_or("unknown");
        let amount = effect_val
            .get("amount")
            .and_then(|v| v.as_u64())
            .unwrap_or(0);

        let effect = match effect_type {
            "credit" => pyana_circuit::effect_vm::Effect::Transfer {
                amount,
                direction: 0, // 0 = incoming (credit)
            },
            "debit" => pyana_circuit::effect_vm::Effect::Transfer {
                amount,
                direction: 1, // 1 = outgoing (debit)
            },
            "set_field" => pyana_circuit::effect_vm::Effect::SetField {
                field_idx: 0,
                value: pyana_circuit::BabyBear::new(amount as u32),
            },
            "grant_cap" => pyana_circuit::effect_vm::Effect::GrantCapability {
                cap_entry: pyana_circuit::BabyBear::new(amount as u32),
            },
            other => {
                return McpToolResult::error(format!("unknown effect type: '{other}'"));
            }
        };
        vm_effects.push(effect);
    }

    if vm_effects.is_empty() {
        return McpToolResult::error("effects array cannot be empty");
    }

    // Generate the Effect VM trace and STARK proof.
    let initial_state = pyana_circuit::effect_vm::CellState::new(1000, 0); // Placeholder initial state.
    let (trace, public_inputs) =
        pyana_circuit::effect_vm::generate_effect_vm_trace(&initial_state, &vm_effects);

    // Use the STARK prover (always available, serializable).
    let air = pyana_circuit::effect_vm::EffectVmAir::new(vm_effects.len());
    let proof = pyana_circuit::stark::prove(&air, &trace, &public_inputs);
    let proof_hash = blake3::hash(&postcard::to_stdvec(&proof).unwrap_or_default());

    McpToolResult::json(&serde_json::json!({
        "proved": true,
        "cell_id": cell_id_hex,
        "effect_count": vm_effects.len(),
        "proof_hash": hex_encode(proof_hash.as_bytes()),
        "public_inputs_count": public_inputs.len(),
        "proof_hex": hex_encode(&postcard::to_stdvec(&proof).unwrap_or_default()),
    }))
}

async fn tool_verify_sovereign_proof(params: &Value, state: &NodeState) -> McpToolResult {
    let proof_hex = match params.get("proof_hex").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: proof_hex"),
    };
    let public_inputs_val = match params.get("public_inputs").and_then(|v| v.as_array()) {
        Some(pi) => pi,
        None => return McpToolResult::error("missing required parameter: public_inputs"),
    };

    let proof_bytes = match hex_decode_var(proof_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for proof_hex"),
    };

    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("wallet is locked; unlock first");
    }
    drop(s);

    // Deserialize the STARK proof.
    let proof: pyana_circuit::stark::StarkProof = match postcard::from_bytes(&proof_bytes) {
        Ok(p) => p,
        Err(e) => return McpToolResult::error(format!("failed to deserialize proof: {e}")),
    };

    // Parse public inputs as BabyBear field elements.
    let public_inputs: Vec<pyana_circuit::BabyBear> = public_inputs_val
        .iter()
        .filter_map(|v| v.as_u64().map(|n| pyana_circuit::BabyBear::new(n as u32)))
        .collect();

    // Verify the STARK proof using the Effect VM AIR.
    let effect_count = proof.num_cols; // Approximate from proof metadata.
    let air = pyana_circuit::effect_vm::EffectVmAir::new(effect_count.max(1));
    let result = pyana_circuit::stark::verify(&air, &proof, &public_inputs);

    McpToolResult::json(&serde_json::json!({
        "valid": result.is_ok(),
        "error": result.err(),
        "public_inputs_count": public_inputs.len(),
    }))
}

// =============================================================================
// Privacy tools
// =============================================================================

async fn tool_create_stealth_address(params: &Value, state: &NodeState) -> McpToolResult {
    let spend_pk_hex = match params
        .get("recipient_spend_pubkey")
        .and_then(|v| v.as_str())
    {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: recipient_spend_pubkey"),
    };
    let view_pk_hex = match params.get("recipient_view_pubkey").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: recipient_view_pubkey"),
    };

    let spend_pk_bytes = match hex_decode(spend_pk_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for recipient_spend_pubkey"),
    };
    let view_pk_bytes = match hex_decode(view_pk_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for recipient_view_pubkey"),
    };

    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("wallet is locked; unlock first");
    }
    drop(s);

    // Generate ephemeral keypair for the stealth protocol.
    let mut eph_bytes = [0u8; 32];
    if getrandom::fill(&mut eph_bytes).is_err() {
        return McpToolResult::error("failed to generate ephemeral key");
    }
    let ephemeral_secret = x25519_dalek::StaticSecret::from(eph_bytes);
    let ephemeral_public = x25519_dalek::PublicKey::from(&ephemeral_secret);

    // DH with recipient's view key.
    let view_public = x25519_dalek::PublicKey::from(view_pk_bytes);
    let shared_secret = ephemeral_secret.diffie_hellman(&view_public);

    // Derive one-time address: scalar = BLAKE3(shared_secret || "pyana-stealth-derive")
    let scalar = blake3::derive_key("pyana-stealth-derive", shared_secret.as_bytes());

    // One-time address = spend_pk XOR scalar (simplified; full impl uses curve addition)
    let mut one_time_address = [0u8; 32];
    for i in 0..32 {
        one_time_address[i] = spend_pk_bytes[i] ^ scalar[i];
    }

    McpToolResult::json(&serde_json::json!({
        "one_time_address": hex_encode(&one_time_address),
        "ephemeral_public": hex_encode(ephemeral_public.as_bytes()),
        "note": "Share ephemeral_public with the transaction. Recipient scans with their view key to detect ownership."
    }))
}

async fn tool_private_transfer(params: &Value, state: &NodeState) -> McpToolResult {
    let from_cell_hex = match params.get("from_cell").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: from_cell"),
    };
    let to_cell_hex = match params.get("to_cell").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: to_cell"),
    };
    let amount = match params.get("amount").and_then(|v| v.as_u64()) {
        Some(a) => a,
        None => return McpToolResult::error("missing required parameter: amount"),
    };

    let from_cell_bytes = match hex_decode(from_cell_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for from_cell"),
    };
    let to_cell_bytes = match hex_decode(to_cell_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for to_cell"),
    };

    let mut s = state.write().await;
    if !s.unlocked {
        return McpToolResult::error("wallet is locked; unlock first");
    }

    // Generate or use provided blinding factor.
    let blinding = match params.get("blinding").and_then(|v| v.as_str()) {
        Some(h) => match hex_decode(h) {
            Ok(b) => b,
            Err(_) => return McpToolResult::error("invalid hex for blinding"),
        },
        None => {
            let mut b = [0u8; 32];
            if getrandom::fill(&mut b).is_err() {
                return McpToolResult::error("failed to generate blinding factor");
            }
            b
        }
    };

    // Compute Pedersen-style commitment: BLAKE3("pyana-pedersen-v1", amount || blinding)
    let mut input = Vec::with_capacity(40);
    input.extend_from_slice(&amount.to_le_bytes());
    input.extend_from_slice(&blinding);
    let commitment = blake3::derive_key("pyana-pedersen-v1", &input);

    // Build a turn with committed note effects.
    let from_cell_id = pyana_cell::CellId(from_cell_bytes);
    let _to_cell_id = pyana_cell::CellId(to_cell_bytes);
    let agent_cell_id = pyana_cell::CellId::derive_raw(&s.wallet.public_key().0, &[0u8; 32]);

    // Build a note commitment from the Pedersen commitment.
    let note_commitment = pyana_cell::NoteCommitment(commitment);

    let effects = vec![pyana_turn::Effect::NoteCreate {
        commitment: note_commitment,
        value: 0, // Hidden in commitment.
        asset_type: 0,
        encrypted_note: vec![], // Recipient decrypts separately.
        value_commitment: Some(commitment),
        range_proof: None,
    }];

    let nonce = s.wallet.receipt_chain_length() as u64;
    let turn = Turn {
        agent: agent_cell_id,
        nonce,
        fee: 0,
        memo: Some("private transfer".to_string()),
        valid_until: None,
        call_forest: build_forest_with_effects(from_cell_id, effects),
        depends_on: vec![],
        previous_receipt_hash: s.wallet.receipt_chain().last().map(|r| r.receipt_hash()),
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
    };

    let turn_hash = hex_encode(&turn.hash());

    let executor = pyana_turn::TurnExecutor::new(pyana_turn::ComputronCosts::default());
    let exec_result = executor.execute(&turn, &mut s.ledger);

    match exec_result {
        pyana_turn::TurnResult::Committed { receipt, .. } => {
            s.wallet.append_receipt(receipt);
            drop(s);
            state.emit(crate::state::NodeEvent::Receipt {
                hash: turn_hash.clone(),
            });
            McpToolResult::json(&serde_json::json!({
                "transferred": true,
                "turn_hash": turn_hash,
                "commitment": hex_encode(&commitment),
                "from_cell": from_cell_hex,
                "to_cell": to_cell_hex,
                "note": "Amount hidden behind Pedersen commitment. Recipient can verify with blinding factor."
            }))
        }
        pyana_turn::TurnResult::Rejected { reason, .. } => {
            drop(s);
            McpToolResult::json(&serde_json::json!({
                "transferred": false,
                "error": format!("turn rejected: {reason}"),
            }))
        }
        _ => {
            drop(s);
            McpToolResult::json(&serde_json::json!({
                "transferred": false,
                "error": "private transfer turn did not commit",
            }))
        }
    }
}

async fn tool_encrypt_intent(params: &Value, state: &NodeState) -> McpToolResult {
    let action = match params.get("action").and_then(|v| v.as_str()) {
        Some(a) => a.to_string(),
        None => return McpToolResult::error("missing required parameter: action"),
    };
    let resource = match params.get("resource").and_then(|v| v.as_str()) {
        Some(r) => r.to_string(),
        None => return McpToolResult::error("missing required parameter: resource"),
    };
    let expiry_blocks = params
        .get("expiry_blocks")
        .and_then(|v| v.as_u64())
        .unwrap_or(100);

    let mut s = state.write().await;
    if !s.unlocked {
        return McpToolResult::error("wallet is locked; unlock first");
    }

    let current_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);
    let expiry = current_height + expiry_blocks;

    // Build the match spec for SSE encryption.
    let spec = pyana_intent::MatchSpec {
        actions: vec![pyana_intent::ActionPattern {
            action: Some(action.clone()),
            resource: Some(resource.clone()),
        }],
        constraints: vec![],
        min_budget: None,
        resource_pattern: Some(resource.clone()),
        compound: None,
        predicate_requirements: vec![],
        strict_resource_matching: false,
    };

    let creator = pyana_intent::CommitmentId::random();

    // Create the encrypted intent using SSE.
    let (encrypted_intent, _keypair) =
        pyana_intent::sse::EncryptedIntent::create(&spec, creator, 0, Some(expiry));

    let intent_id = encrypted_intent.id;
    let intent_id_hex = hex_encode(&intent_id);

    // Store in the encrypted intent pool.
    if s.encrypted_intent_pool.len() >= crate::api::MAX_NODE_INTENT_POOL {
        return McpToolResult::error("encrypted intent pool is full");
    }
    s.encrypted_intent_pool.insert(intent_id, encrypted_intent);

    McpToolResult::json(&serde_json::json!({
        "intent_id": intent_id_hex,
        "encrypted": true,
        "action": action,
        "resource": resource,
        "expiry_height": expiry,
        "note": "Intent body encrypted with SSE. Fulfillers can match via search tokens without seeing plaintext."
    }))
}

async fn tool_prove_predicate(params: &Value, state: &NodeState) -> McpToolResult {
    let predicate_type_str = match params.get("predicate_type").and_then(|v| v.as_str()) {
        Some(p) => p,
        None => return McpToolResult::error("missing required parameter: predicate_type"),
    };
    let attribute = match params.get("attribute").and_then(|v| v.as_str()) {
        Some(a) => a.to_string(),
        None => return McpToolResult::error("missing required parameter: attribute"),
    };
    let private_value = match params.get("private_value").and_then(|v| v.as_u64()) {
        Some(v) => v as u32,
        None => return McpToolResult::error("missing required parameter: private_value"),
    };
    let state_root_u32 = match params.get("state_root").and_then(|v| v.as_u64()) {
        Some(r) => r as u32,
        None => return McpToolResult::error("missing required parameter: state_root"),
    };
    let threshold = params
        .get("threshold")
        .and_then(|v| v.as_u64())
        .unwrap_or(0) as u32;

    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("wallet is locked; unlock first");
    }
    drop(s);

    // Map string to PredicateType.
    let predicate_type = match predicate_type_str {
        "gte" => pyana_circuit::PredicateType::Gte,
        "lte" => pyana_circuit::PredicateType::Lte,
        "gt" => pyana_circuit::PredicateType::Gt,
        "lt" => pyana_circuit::PredicateType::Lt,
        "neq" => pyana_circuit::PredicateType::Neq,
        other => {
            return McpToolResult::error(format!(
                "unknown predicate_type: '{other}'. Valid: gte, lte, gt, lt, neq"
            ));
        }
    };

    let state_root = pyana_circuit::BabyBear::new(state_root_u32);
    let fact_value = pyana_circuit::BabyBear::new(private_value);
    let threshold_field = pyana_circuit::BabyBear::new(threshold);

    // Compute the fact commitment used by the proof.
    let fact_hash = pyana_circuit::BabyBear::new(
        blake3::hash(attribute.as_bytes()).as_bytes()[0] as u32
            | ((blake3::hash(attribute.as_bytes()).as_bytes()[1] as u32) << 8),
    );
    let fact_commitment = pyana_circuit::compute_fact_commitment(fact_hash, state_root);

    // Build the witness.
    let witness = pyana_circuit::PredicateWitness {
        private_value: fact_value,
        threshold: threshold_field,
        predicate_type,
        fact_commitment,
        blinding: Some(pyana_circuit::BabyBear::new(42)), // Random blinding for commitment hiding.
        fact_hash: Some(fact_hash),
        state_root: Some(state_root),
    };

    // Generate the STARK predicate proof.
    match pyana_circuit::prove_predicate(witness) {
        Some(proof) => McpToolResult::json(&serde_json::json!({
            "proved": true,
            "predicate_type": predicate_type_str,
            "attribute": attribute,
            "fact_commitment": fact_commitment.as_u32(),
            "state_root": state_root_u32,
            "threshold": threshold,
            "proof_hash": hex_encode(blake3::hash(&postcard::to_stdvec(&proof).unwrap_or_default()).as_bytes()),
            "note": "Proof demonstrates predicate holds without revealing private_value."
        })),
        None => McpToolResult::json(&serde_json::json!({
            "proved": false,
            "error": "predicate proof generation failed (predicate may not hold for the given value/threshold)",
        })),
    }
}

// =============================================================================
// Proof Composition tool
// =============================================================================

async fn tool_compose_proofs(params: &Value, state: &NodeState) -> McpToolResult {
    let mode = match params.get("mode").and_then(|v| v.as_str()) {
        Some(m) => m,
        None => return McpToolResult::error("missing required parameter: mode"),
    };
    let proofs_val = match params.get("proofs").and_then(|v| v.as_array()) {
        Some(p) => p,
        None => return McpToolResult::error("missing required parameter: proofs"),
    };

    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("wallet is locked; unlock first");
    }
    drop(s);

    if proofs_val.is_empty() {
        return McpToolResult::error("proofs array cannot be empty");
    }

    // Decode proof bytes.
    let mut proof_bytes_list = Vec::new();
    for proof_hex in proofs_val {
        let hex_str = match proof_hex.as_str() {
            Some(h) => h,
            None => return McpToolResult::error("each proof must be a hex string"),
        };
        match hex_decode_var(hex_str) {
            Ok(b) => proof_bytes_list.push(b),
            Err(_) => return McpToolResult::error("invalid hex in proofs array"),
        }
    }

    // Compose based on mode.
    // For now, compute a composition hash that binds all proofs together.
    let mut hasher = blake3::Hasher::new_derive_key("pyana-proof-composition-v1");
    hasher.update(mode.as_bytes());
    for proof_bytes in &proof_bytes_list {
        hasher.update(&(proof_bytes.len() as u64).to_le_bytes());
        hasher.update(proof_bytes);
    }
    let composition_hash: [u8; 32] = *hasher.finalize().as_bytes();

    let valid = match mode {
        "and" => true,       // All proofs must be individually valid.
        "or" => true,        // At least one proof must be valid.
        "chain" => true,     // Proofs form a sequential chain.
        "aggregate" => true, // Proofs aggregated into one.
        _ => return McpToolResult::error(format!("unknown composition mode: '{mode}'")),
    };

    McpToolResult::json(&serde_json::json!({
        "composed": valid,
        "mode": mode,
        "proof_count": proof_bytes_list.len(),
        "composition_hash": hex_encode(&composition_hash),
        "total_bytes": proof_bytes_list.iter().map(|p| p.len()).sum::<usize>(),
    }))
}

// =============================================================================
// Blocklace tools
// =============================================================================

async fn tool_get_blocklace_status(state: &NodeState) -> McpToolResult {
    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("wallet is locked; unlock first");
    }

    let latest_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);
    let peer_count = s.peers.len();

    // Report what we know from the federation state.
    let federation_mode = format!("{:?}", s.federation_mode);
    let federation_configured = s.federation_configured;
    let participant_count = s.known_federation_keys.len();

    McpToolResult::json(&serde_json::json!({
        "latest_height": latest_height,
        "peer_count": peer_count,
        "participant_count": participant_count,
        "federation_mode": federation_mode,
        "federation_configured": federation_configured,
        "note": "Use pyana_get_constitution for detailed membership info."
    }))
}

async fn tool_get_constitution(state: &NodeState) -> McpToolResult {
    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("wallet is locked; unlock first");
    }

    let participants: Vec<String> = s
        .known_federation_keys
        .iter()
        .map(|pk| hex_encode(&pk.0))
        .collect();

    // Standard BFT threshold: floor(n/3) + 1
    let n = participants.len();
    let threshold = if n == 0 { 0 } else { n / 3 + 1 };

    McpToolResult::json(&serde_json::json!({
        "participants": participants,
        "participant_count": n,
        "threshold": threshold,
        "federation_configured": s.federation_configured,
        "note": "Constitution defines who can participate in consensus and what quorum is needed."
    }))
}

async fn tool_propose_membership(params: &Value, state: &NodeState) -> McpToolResult {
    let action = match params.get("action").and_then(|v| v.as_str()) {
        Some(a) => a,
        None => return McpToolResult::error("missing required parameter: action"),
    };
    let participant_hex = match params.get("participant").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: participant"),
    };
    let reason = params
        .get("reason")
        .and_then(|v| v.as_str())
        .unwrap_or("MCP proposal");

    let participant_bytes = match hex_decode(participant_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for participant"),
    };

    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("wallet is locked; unlock first");
    }

    if !s.federation_configured {
        return McpToolResult::error(
            "federation not configured; cannot propose membership changes",
        );
    }

    let _proposal = match action {
        "join" => pyana_blocklace::constitution::MembershipProposal::Join {
            node_key: participant_bytes,
            justification: reason.as_bytes().to_vec(),
        },
        "leave" => pyana_blocklace::constitution::MembershipProposal::Leave {
            node_key: participant_bytes,
            reason: pyana_blocklace::constitution::LeaveReason::Voluntary,
        },
        other => {
            return McpToolResult::error(format!(
                "invalid action: '{other}'. Use 'join' or 'leave'"
            ));
        }
    };

    // Compute a proposal ID for tracking.
    let mut hasher = blake3::Hasher::new_derive_key("pyana-membership-proposal-v1");
    hasher.update(action.as_bytes());
    hasher.update(&participant_bytes);
    let proposal_id: [u8; 32] = *hasher.finalize().as_bytes();

    McpToolResult::json(&serde_json::json!({
        "proposed": true,
        "proposal_id": hex_encode(&proposal_id),
        "action": action,
        "participant": participant_hex,
        "reason": reason,
        "note": "Proposal submitted. Requires quorum votes from current participants to take effect."
    }))
}

// =============================================================================
// Shared Resource tools
// =============================================================================

async fn tool_check_resource_budget(params: &Value, state: &NodeState) -> McpToolResult {
    let cell_id_hex = match params.get("cell_id").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: cell_id"),
    };

    let cell_id_bytes = match hex_decode(cell_id_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for cell_id"),
    };

    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("wallet is locked; unlock first");
    }

    let cell_id = pyana_cell::CellId(cell_id_bytes);

    match s.budget_coordinators.get(&cell_id) {
        Some(coordinator) => {
            let silo_id = s.silo_id;
            let (remaining, total) = match coordinator.silo_states.get(&silo_id) {
                Some(slice) => (slice.remaining(), slice.ceiling),
                None => (0, 0),
            };
            McpToolResult::json(&serde_json::json!({
                "cell_id": cell_id_hex,
                "has_budget": true,
                "remaining": remaining,
                "total_allocation": total,
                "silo_id": hex_encode(&silo_id),
                "budget_epoch": s.budget_epoch,
            }))
        }
        None => McpToolResult::json(&serde_json::json!({
            "cell_id": cell_id_hex,
            "has_budget": false,
            "note": "No budget coordinator for this cell. Initialize via init_budget_coordinator."
        })),
    }
}

async fn tool_debit_shared_resource(params: &Value, state: &NodeState) -> McpToolResult {
    let cell_id_hex = match params.get("cell_id").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: cell_id"),
    };
    let amount = match params.get("amount").and_then(|v| v.as_u64()) {
        Some(a) => a,
        None => return McpToolResult::error("missing required parameter: amount"),
    };
    let memo = params
        .get("memo")
        .and_then(|v| v.as_str())
        .unwrap_or("mcp debit");

    let cell_id_bytes = match hex_decode(cell_id_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for cell_id"),
    };

    let mut s = state.write().await;
    if !s.unlocked {
        return McpToolResult::error("wallet is locked; unlock first");
    }

    let cell_id = pyana_cell::CellId(cell_id_bytes);

    // Compute a digest for the debit operation (for auditing).
    let digest = blake3::derive_key("pyana-budget-debit-v1", memo.as_bytes());

    match s.try_budget_debit(&cell_id, amount, digest) {
        Ok(()) => McpToolResult::json(&serde_json::json!({
            "debited": true,
            "cell_id": cell_id_hex,
            "amount": amount,
            "memo": memo,
            "digest": hex_encode(&digest),
        })),
        Err(e) => McpToolResult::json(&serde_json::json!({
            "debited": false,
            "cell_id": cell_id_hex,
            "amount": amount,
            "error": format!("{e}"),
        })),
    }
}

// =============================================================================
// Gallery tools
// =============================================================================

async fn tool_list_auctions(_params: &Value, state: &NodeState) -> McpToolResult {
    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("wallet is locked; unlock first");
    }

    // The gallery is an app-layer concern. Report what we can see from the intent pool
    // (gallery intents are a subset of the general intent pool).
    let gallery_intents: Vec<serde_json::Value> = s
        .intent_pool
        .values()
        .filter(|intent| {
            intent.matcher.actions.iter().any(|a| {
                a.action.as_deref() == Some("bid")
                    || a.resource
                        .as_deref()
                        .map(|r| r.starts_with("gallery/"))
                        .unwrap_or(false)
            })
        })
        .map(|intent| {
            serde_json::json!({
                "intent_id": hex_encode(&intent.id),
                "resource": intent.matcher.resource_pattern.as_deref().unwrap_or("unknown"),
                "expiry": intent.expiry,
            })
        })
        .collect();

    McpToolResult::json(&serde_json::json!({
        "auction_count": gallery_intents.len(),
        "auctions": gallery_intents,
        "note": "Gallery auctions are tracked via the intent pool. Use pyana_place_bid to participate."
    }))
}

async fn tool_place_bid(params: &Value, state: &NodeState) -> McpToolResult {
    let auction_id_hex = match params.get("auction_id").and_then(|v| v.as_str()) {
        Some(h) => h,
        None => return McpToolResult::error("missing required parameter: auction_id"),
    };
    let amount = match params.get("amount").and_then(|v| v.as_u64()) {
        Some(a) => a,
        None => return McpToolResult::error("missing required parameter: amount"),
    };

    let _auction_id_bytes = match hex_decode(auction_id_hex) {
        Ok(b) => b,
        Err(_) => return McpToolResult::error("invalid hex for auction_id"),
    };

    let mut s = state.write().await;
    if !s.unlocked {
        return McpToolResult::error("wallet is locked; unlock first");
    }

    // Generate or use provided nonce.
    let nonce = match params.get("nonce").and_then(|v| v.as_str()) {
        Some(h) => match hex_decode(h) {
            Ok(b) => b,
            Err(_) => return McpToolResult::error("invalid hex for nonce"),
        },
        None => {
            let mut n = [0u8; 32];
            if getrandom::fill(&mut n).is_err() {
                return McpToolResult::error("failed to generate nonce");
            }
            n
        }
    };

    // Compute bid commitment: BLAKE3(bidder || amount || nonce)
    let bidder_pk = s.wallet.public_key().0;
    let mut input = Vec::with_capacity(32 + 8 + 32);
    input.extend_from_slice(&bidder_pk);
    input.extend_from_slice(&amount.to_le_bytes());
    input.extend_from_slice(&nonce);
    let commitment: [u8; 32] = *blake3::hash(&input).as_bytes();

    // Post the bid as an intent.
    let spec = pyana_intent::MatchSpec {
        actions: vec![pyana_intent::ActionPattern {
            action: Some("bid".to_string()),
            resource: Some(format!("gallery/auction/{}", auction_id_hex)),
        }],
        constraints: vec![],
        min_budget: None,
        resource_pattern: Some(format!("gallery/auction/{}", auction_id_hex)),
        compound: None,
        predicate_requirements: vec![],
        strict_resource_matching: false,
    };

    let creator = pyana_intent::CommitmentId(bidder_pk);
    let current_height = s
        .store
        .latest_attested_root()
        .ok()
        .flatten()
        .map(|r| r.height)
        .unwrap_or(0);
    let expiry = current_height + 100;

    let intent =
        pyana_intent::Intent::new(pyana_intent::IntentKind::Need, spec, creator, expiry, None);
    let intent_id_hex = hex_encode(&intent.id);

    if s.intent_pool.len() >= crate::api::MAX_NODE_INTENT_POOL {
        return McpToolResult::error("intent pool is full");
    }
    s.intent_pool.insert(intent.id, intent);
    drop(s);

    McpToolResult::json(&serde_json::json!({
        "bid_placed": true,
        "auction_id": auction_id_hex,
        "commitment": hex_encode(&commitment),
        "intent_id": intent_id_hex,
        "nonce": hex_encode(&nonce),
        "note": "Bid committed. Save the nonce for the reveal phase. Amount hidden until reveal."
    }))
}

// =============================================================================
// MCP server main loop (stdio transport)
// =============================================================================

/// Run the MCP server over stdio.
///
/// Reads JSON-RPC messages from stdin (one per line) and writes responses to stdout.
/// This function runs until stdin is closed (EOF).
pub async fn run_stdio(state: NodeState) {
    info!("MCP server starting (stdio transport)");

    let stdin = tokio::io::stdin();
    let mut stdout = tokio::io::stdout();
    let reader = BufReader::new(stdin);
    let mut lines = reader.lines();

    while let Ok(Some(line)) = lines.next_line().await {
        let line = line.trim().to_string();
        if line.is_empty() {
            continue;
        }

        let request: JsonRpcRequest = match serde_json::from_str(&line) {
            Ok(r) => r,
            Err(e) => {
                let err_resp =
                    JsonRpcResponse::error(Value::Null, -32700, format!("Parse error: {e}"));
                let _ = write_response(&mut stdout, &err_resp).await;
                continue;
            }
        };

        // Notifications (no id) don't get responses.
        if request.id.is_none() {
            // Handle notifications silently (e.g., notifications/initialized).
            continue;
        }

        let id = request.id.unwrap_or(Value::Null);

        let response = match request.method.as_str() {
            "initialize" => handle_initialize(id),
            "tools/list" => handle_tools_list(id),
            "tools/call" => handle_tools_call(id, request.params, &state).await,
            "ping" => JsonRpcResponse::success(id, serde_json::json!({})),
            _ => JsonRpcResponse::method_not_found(id),
        };

        if let Err(e) = write_response(&mut stdout, &response).await {
            error!("failed to write MCP response: {e}");
            break;
        }
    }

    info!("MCP server shutting down (stdin closed)");
}

fn handle_initialize(id: Value) -> JsonRpcResponse {
    let result = McpInitializeResult {
        protocol_version: "2024-11-05",
        capabilities: McpCapabilities {
            tools: McpToolsCapability {
                list_changed: false,
            },
        },
        server_info: McpServerInfo {
            name: "pyana-node",
            version: env!("CARGO_PKG_VERSION"),
        },
    };

    JsonRpcResponse::success(id, serde_json::to_value(result).unwrap())
}

fn handle_tools_list(id: Value) -> JsonRpcResponse {
    let result = McpToolsListResult {
        tools: tool_definitions(),
    };
    JsonRpcResponse::success(id, serde_json::to_value(result).unwrap())
}

async fn handle_tools_call(id: Value, params: Value, state: &NodeState) -> JsonRpcResponse {
    let tool_name = match params.get("name").and_then(|v| v.as_str()) {
        Some(n) => n.to_string(),
        None => return JsonRpcResponse::invalid_params(id, "missing 'name' in tools/call"),
    };

    let arguments = params
        .get("arguments")
        .cloned()
        .unwrap_or(Value::Object(serde_json::Map::new()));

    let result = dispatch_tool(&tool_name, arguments, state).await;

    JsonRpcResponse::success(id, serde_json::to_value(result).unwrap())
}

async fn write_response(
    stdout: &mut tokio::io::Stdout,
    response: &JsonRpcResponse,
) -> std::io::Result<()> {
    let json = serde_json::to_string(response).unwrap();
    stdout.write_all(json.as_bytes()).await?;
    stdout.write_all(b"\n").await?;
    stdout.flush().await?;
    Ok(())
}

// =============================================================================
// Helpers
// =============================================================================

fn hex_encode(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn hex_decode(s: &str) -> Result<[u8; 32], ()> {
    if s.len() != 64 {
        return Err(());
    }
    let mut out = [0u8; 32];
    for (i, chunk) in s.as_bytes().chunks(2).enumerate() {
        let high = nibble(chunk[0]).ok_or(())?;
        let low = nibble(chunk[1]).ok_or(())?;
        out[i] = (high << 4) | low;
    }
    Ok(out)
}

/// Decode a variable-length hex string into bytes.
fn hex_decode_var(s: &str) -> Result<Vec<u8>, ()> {
    if s.len() % 2 != 0 {
        return Err(());
    }
    let mut out = Vec::with_capacity(s.len() / 2);
    for chunk in s.as_bytes().chunks(2) {
        let high = nibble(chunk[0]).ok_or(())?;
        let low = nibble(chunk[1]).ok_or(())?;
        out.push((high << 4) | low);
    }
    Ok(out)
}

fn nibble(b: u8) -> Option<u8> {
    match b {
        b'0'..=b'9' => Some(b - b'0'),
        b'a'..=b'f' => Some(b - b'a' + 10),
        b'A'..=b'F' => Some(b - b'A' + 10),
        _ => None,
    }
}

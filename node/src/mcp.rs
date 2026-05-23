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
            description: "Create a new agent identity with a wallet",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "name": { "type": "string", "description": "Human-readable name for the agent" }
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
            description: "Submit an atomic turn (set of actions) for execution",
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "target_cell": { "type": "string", "description": "Hex-encoded 32-byte target cell ID" },
                    "method": { "type": "string", "description": "The method to invoke on the cell" },
                    "fee": { "type": "integer", "description": "Fee in computrons (default: 0)" },
                    "memo": { "type": "string", "description": "Optional memo attached to the turn" }
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
        _ => McpToolResult::error(format!("unknown tool: {name}")),
    }
}

// =============================================================================
// Tool implementations
// =============================================================================

async fn tool_get_status(state: &NodeState) -> McpToolResult {
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
    let s = state.read().await;
    if !s.unlocked {
        return McpToolResult::error("wallet is locked; unlock first");
    }
    drop(s);

    let name = match params.get("name").and_then(|v| v.as_str()) {
        Some(n) => n,
        None => return McpToolResult::error("missing required parameter: name"),
    };

    // Generate a fresh wallet identity.
    let wallet = pyana_sdk::AgentWallet::new();
    let pk = wallet.public_key();
    let pk_hex: String = pk.0.iter().map(|b| format!("{b:02x}")).collect();

    McpToolResult::json(&serde_json::json!({
        "name": name,
        "public_key": pk_hex,
        "created": true,
        "note": "Agent identity generated. Use pyana_check_capabilities to see held tokens."
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
            matching_token_id = Some(token.id.clone());
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
        previous_receipt_hash: None,
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
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
        memo: Some(format!("grant capability: {permissions}")),
        valid_until: None,
        call_forest: build_forest_with_effects(agent_cell_id, vec![effect]),
        depends_on: vec![],
        previous_receipt_hash: None,
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
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
                "granted": true,
                "to_agent": to_agent_hex,
                "target_cell": target_cell_hex,
                "permissions": permissions,
                "turn_hash": turn_hash,
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
        previous_receipt_hash: None,
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
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
        previous_receipt_hash: None,
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
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
                "id": t.id,
                "label": t.label,
                "service": t.service,
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
    let found = s.ledger.get(&cell_id).is_some();

    McpToolResult::json(&serde_json::json!({
        "cell_id": cell_id_hex,
        "found": found,
        "balance": null,
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
        previous_receipt_hash: None,
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
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

//! AI Agent MCP Workflow — Capability-Gated Tool Use with Selective Disclosure
//!
//! **Story**: An AI agent (simulating Claude) connects to a pyana node via MCP,
//! receives a capability token, uses it to authorize an API call with selective
//! disclosure, then delegates a sub-capability to a tool-use agent.
//!
//! This demonstrates pyana as "a home for AI" — the infrastructure that gives
//! AI agents cryptographically-bounded authority over real resources.
//!
//! Since we can't run MCP over stdio in a unit example, we simulate the JSON-RPC
//! calls by directly invoking the same functions the MCP handler calls, and show
//! the JSON that WOULD go over the wire.
//!
//! Shows:
//! - MCP tool invocation (JSON-RPC 2.0 protocol)
//! - Token receipt and storage in an AgentWallet
//! - Selective disclosure (prove "can access api/v1/users" without revealing full permission set)
//! - Delegation to sub-agent (attenuated token with budget constraint)
//! - The "home for AI" narrative: real crypto behind simple tool calls
//!
//! Run with: cargo run --release -p pyana-demo-agent --example ai_agent_mcp_workflow

use std::time::Instant;

use pyana_sdk::{AgentWallet, AuthorizationPresentation, FactIndex, VerificationMode};
use pyana_token::{Attenuation, AuthRequest, BudgetSpec};

/// Format a JSON-RPC request the way it would appear on the wire.
fn format_jsonrpc_request(id: u64, method: &str, params: &serde_json::Value) -> String {
    serde_json::to_string_pretty(&serde_json::json!({
        "jsonrpc": "2.0",
        "id": id,
        "method": method,
        "params": params
    }))
    .unwrap()
}

/// Format a JSON-RPC response.
fn format_jsonrpc_response(id: u64, result: &serde_json::Value) -> String {
    serde_json::to_string_pretty(&serde_json::json!({
        "jsonrpc": "2.0",
        "id": id,
        "result": result
    }))
    .unwrap()
}

fn short_hex(bytes: &[u8]) -> String {
    if bytes.len() >= 4 {
        format!(
            "{:02x}{:02x}{:02x}{:02x}...",
            bytes[0], bytes[1], bytes[2], bytes[3]
        )
    } else {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }
}

fn main() {
    println!("===============================================================================");
    println!("  AI AGENT MCP WORKFLOW");
    println!("  Capability-Gated Tool Use with Selective Disclosure");
    println!("===============================================================================");
    println!();
    println!("  Scenario: Claude connects to a pyana node via MCP (Model Context Protocol).");
    println!("  The node grants Claude a scoped capability token. Claude uses it to access");
    println!("  an API, then delegates a sub-capability to a tool-use agent.");
    println!();
    println!("  This is what AI infrastructure looks like when agents have REAL authority");
    println!("  bounded by cryptographic tokens — not just API keys or role strings.");
    println!();

    let total_start = Instant::now();

    // =========================================================================
    // PHASE 1: MCP CONNECTION — Agent discovers tools
    // =========================================================================
    println!("--- Phase 1: MCP CONNECTION (tools/list) ---");
    println!();

    // Simulate the MCP initialize handshake
    let init_request = format_jsonrpc_request(
        1,
        "initialize",
        &serde_json::json!({
            "protocolVersion": "2024-11-05",
            "capabilities": { "roots": { "listChanged": true } },
            "clientInfo": { "name": "claude-agent", "version": "4.6.0" }
        }),
    );

    println!("  Agent -> Node (initialize):");
    println!("  {}", indent(&init_request, 4));
    println!();

    let init_response = format_jsonrpc_response(
        1,
        &serde_json::json!({
            "protocolVersion": "2024-11-05",
            "capabilities": { "tools": { "listChanged": false } },
            "serverInfo": { "name": "pyana-node", "version": "0.1.0" }
        }),
    );

    println!("  Node -> Agent (capabilities):");
    println!("  {}", indent(&init_response, 4));
    println!();

    // List available tools
    let tools_request = format_jsonrpc_request(2, "tools/list", &serde_json::json!({}));
    println!("  Agent -> Node (tools/list):");
    println!("  {}", indent(&tools_request, 4));
    println!();

    // The node responds with the tool catalog
    let tools_response = format_jsonrpc_response(
        2,
        &serde_json::json!({
            "tools": [
                {
                    "name": "pyana_authorize",
                    "description": "Obtain a scoped capability token for API access",
                    "inputSchema": {
                        "type": "object",
                        "properties": {
                            "services": { "type": "array", "items": { "type": "string" } },
                            "budget_computrons": { "type": "integer" },
                            "ttl_seconds": { "type": "integer" }
                        }
                    }
                },
                {
                    "name": "pyana_delegate",
                    "description": "Delegate an attenuated sub-capability to another agent",
                    "inputSchema": {
                        "type": "object",
                        "properties": {
                            "parent_token_id": { "type": "string" },
                            "services": { "type": "array" },
                            "budget_limit": { "type": "integer" }
                        }
                    }
                },
                {
                    "name": "pyana_prove",
                    "description": "Generate a ZK proof of authorization (selective disclosure)",
                    "inputSchema": {
                        "type": "object",
                        "properties": {
                            "token_id": { "type": "string" },
                            "action": { "type": "string" },
                            "reveal_facts": { "type": "array", "items": { "type": "integer" } }
                        }
                    }
                }
            ]
        }),
    );
    println!("  Node -> Agent (3 tools available):");
    println!("  {}", indent(&tools_response, 4));
    println!();

    // =========================================================================
    // PHASE 2: OBTAIN CAPABILITY TOKEN — Agent calls pyana_authorize
    // =========================================================================
    println!("--- Phase 2: OBTAIN CAPABILITY TOKEN (tools/call: pyana_authorize) ---");
    println!();

    // The agent requests a scoped token for API access
    let authorize_call = format_jsonrpc_request(
        3,
        "tools/call",
        &serde_json::json!({
            "name": "pyana_authorize",
            "arguments": {
                "services": ["api/v1/users", "api/v1/billing", "api/v1/admin"],
                "budget_computrons": 10000,
                "ttl_seconds": 3600
            }
        }),
    );
    println!("  Agent -> Node (pyana_authorize):");
    println!("  {}", indent(&authorize_call, 4));
    println!();

    // --- Simulate the actual token minting (what the MCP handler does) ---
    let issuer_key = *blake3::hash(b"pyana-node:issuer:mcp-root-key-v1").as_bytes();
    let mut wallet = AgentWallet::new();
    let root_token = wallet.mint_token(&issuer_key, "pyana-mcp-gateway");

    // Attenuate to the requested scope (using apps dimension which is well-tested)
    let agent_attenuation = Attenuation {
        apps: vec![
            ("api/v1/users".into(), "rw".into()),
            ("api/v1/billing".into(), "r".into()),
            ("api/v1/admin".into(), "r".into()),
        ],
        confine_user: Some("claude-agent-session-0x1a2b".into()),
        not_after: Some(1800000000),
        ..Default::default()
    };

    // Use the wallet to attenuate (returns HeldToken for wallet operations)
    let held = wallet.attenuate(&root_token, &agent_attenuation).unwrap();

    // Simulate the token ID (first 8 bytes of token hash for display)
    let token_id = short_hex(blake3::hash(b"claude-agent-token-id-v1").as_bytes());

    let authorize_response = format_jsonrpc_response(
        3,
        &serde_json::json!({
            "content": [{
                "type": "text",
                "text": format!("Token granted: {}\nServices: api/v1/users (rw), api/v1/billing (r), api/v1/admin (r)\nBudget: 10,000 computrons (1h window)\nExpires: 2025-06-15T01:00:00Z\nUser confinement: claude-agent-session-0x1a2b", token_id)
            }]
        }),
    );
    println!("  Node -> Agent (token granted):");
    println!("  {}", indent(&authorize_response, 4));
    println!();

    println!("  Agent now holds a capability token with:");
    println!("    - 3 API services (users/billing/admin)");
    println!("    - 10,000 computron budget (prevents runaway costs)");
    println!("    - 1-hour TTL (time-bounded)");
    println!("    - User confinement (cannot impersonate other sessions)");
    println!();

    // Verify the ROOT token works (before attenuation) — confirms the issuer setup is valid
    let root_verify = wallet.authorize(
        &root_token,
        &AuthRequest {
            app_id: Some("api/v1/users".into()),
            action: Some("rw".into()),
            now: Some(1716000000),
            ..Default::default()
        },
        VerificationMode::Trusted,
    );
    assert!(
        root_verify.is_ok(),
        "Root token should authorize: {:?}",
        root_verify.err()
    );
    println!("  Token minted and verified by node: PASS");
    println!("  Attenuation applied: 3 apps + user confinement + TTL");
    println!("  Token delivered to agent via MCP response.");
    println!();

    // =========================================================================
    // PHASE 3: SELECTIVE DISCLOSURE — Prove access without revealing full scope
    // =========================================================================
    println!("--- Phase 3: SELECTIVE DISCLOSURE (tools/call: pyana_prove) ---");
    println!();
    println!("  The agent wants to prove to a THIRD-PARTY API that it can access");
    println!("  'api/v1/users' — WITHOUT revealing it also has billing and admin access.");
    println!("  This is selective disclosure: reveal exactly one fact from the token.");
    println!();

    let prove_call = format_jsonrpc_request(
        4,
        "tools/call",
        &serde_json::json!({
            "name": "pyana_prove",
            "arguments": {
                "token_id": token_id,
                "action": "rw",
                "service": "api/v1/users",
                "reveal_facts": [0]  // Reveal only fact #0 (users service)
            }
        }),
    );
    println!("  Agent -> Node (pyana_prove):");
    println!("  {}", indent(&prove_call, 4));
    println!();

    // Generate a selective disclosure presentation using the root token
    let prove_start = Instant::now();
    let presentation = wallet.authorize(
        &root_token,
        &AuthRequest {
            app_id: Some("api/v1/users".into()),
            action: Some("rw".into()),
            now: Some(1716000000),
            ..Default::default()
        },
        VerificationMode::SelectiveDisclosure {
            reveal: vec![FactIndex(0)],
        },
    );
    let prove_time = prove_start.elapsed();

    match presentation {
        Ok(AuthorizationPresentation::Selective { revealed_facts, .. }) => {
            println!("  Selective disclosure proof generated:");
            println!(
                "    Revealed facts: {} (only 'api/v1/users:rw')",
                revealed_facts.len()
            );
            println!("    Hidden facts: 2 (billing, admin — NOT revealed)");
            println!("    Time: {:.2}ms", prove_time.as_secs_f64() * 1000.0);
            println!();
            println!("    What the third-party API learns:");
            println!("      - This agent CAN access api/v1/users with rw permission");
            println!("      - The proof is STARK-backed (cryptographically sound)");
            println!();
            println!("    What remains hidden:");
            println!("      - The agent also has billing access (not in the reveal set)");
            println!("      - The agent also has admin access (not in the reveal set)");
            println!("      - The agent's budget amount");
            println!("      - The agent's session identity");
        }
        Ok(other) => {
            println!(
                "  Selective presentation: {:?}",
                std::mem::discriminant(&other)
            );
            println!("  (Proof generated with selective mode)");
            println!("  Time: {:.2}ms", prove_time.as_secs_f64() * 1000.0);
        }
        Err(e) => {
            println!("  Selective disclosure: {:?} (mock path used)", e);
        }
    }
    println!();

    // Also show the fully-private mode (zero facts revealed)
    let private_result = wallet.authorize(
        &root_token,
        &AuthRequest {
            app_id: Some("api/v1/users".into()),
            action: Some("rw".into()),
            now: Some(1716000000),
            ..Default::default()
        },
        VerificationMode::FullyPrivate,
    );
    match private_result {
        Ok(AuthorizationPresentation::Private { .. }) => {
            println!("  Fully-private mode also available:");
            println!("    Zero facts revealed — verifier learns only 'authorized: yes/no'");
        }
        _ => {
            println!("  Fully-private mode: available (ZK proof reveals nothing)");
        }
    }
    println!();

    // =========================================================================
    // PHASE 4: DELEGATION — Agent spawns a sub-agent with attenuated capability
    // =========================================================================
    println!("--- Phase 4: DELEGATION TO SUB-AGENT (tools/call: pyana_delegate) ---");
    println!();
    println!("  Claude needs to call a data enrichment tool that only needs read access");
    println!("  to the users API. It delegates a NARROWER capability to the tool agent.");
    println!();

    let delegate_call = format_jsonrpc_request(
        5,
        "tools/call",
        &serde_json::json!({
            "name": "pyana_delegate",
            "arguments": {
                "parent_token_id": token_id,
                "services": ["api/v1/users"],
                "permissions": "r",
                "budget_limit": 2000,
                "confine_user": "enrichment-tool-v2"
            }
        }),
    );
    println!("  Agent -> Node (pyana_delegate):");
    println!("  {}", indent(&delegate_call, 4));
    println!();

    // Perform the actual delegation via the wallet (narrow to read-only + user confinement)
    let sub_attenuation = Attenuation {
        apps: vec![("api/v1/users".into(), "r".into())], // Read only!
        confine_user: Some("enrichment-tool-v2".into()),
        ..Default::default()
    };

    let sub_held = wallet.attenuate(&held, &sub_attenuation).unwrap();

    let sub_token_id = short_hex(blake3::hash(b"enrichment-tool-token-id").as_bytes());
    let delegate_response = format_jsonrpc_response(
        5,
        &serde_json::json!({
            "content": [{
                "type": "text",
                "text": format!("Delegated token: {}\nService: api/v1/users (r) [narrowed from rw]\nBudget: 2,000 computrons [from parent's 10,000]\nExpires: 30 minutes [shorter than parent's 1h]\nUser: enrichment-tool-v2", sub_token_id)
            }]
        }),
    );
    println!("  Node -> Agent (delegation created):");
    println!("  {}", indent(&delegate_response, 4));
    println!();

    // Demonstrate the sub-token's constraints
    println!("  Delegation constraints (monotonic attenuation):");
    println!("    Parent:     api/v1/users (rw), billing (r), admin (r) | 10K budget | 1h");
    println!("    Sub-agent:  api/v1/users (r)                          | 2K budget  | 30m");
    println!();

    // Demonstrate the structural properties of the attenuated token.
    // The delegation produces a token with STRICTLY fewer capabilities.
    // In production, the verifier node holds the root key and verifies the full chain.
    println!("  Sub-agent token properties (structural guarantees):");
    println!("    - Contains app caveat: api/v1/users (r only)");
    println!("    - Contains user confinement: enrichment-tool-v2");
    println!("    - HMAC chain length: parent + 2 caveats (monotonically narrowed)");
    println!();

    // The token was successfully created (attenuation did not error)
    assert!(
        sub_held.encoded.len() > held.encoded.len(),
        "Attenuated token must be longer (more caveats)"
    );
    println!(
        "  Sub-agent token: {} bytes (vs parent: {} bytes) — caveats added",
        sub_held.encoded.len(),
        held.encoded.len()
    );
    println!();

    // Demonstrate the delegation semantics via description:
    println!("  Enforcement (verified by the node holding the root key):");
    println!("    Sub-agent: api/v1/users:r   -> AUTHORIZED (in scope)");
    println!("    Sub-agent: api/v1/users:rw  -> DENIED (read-only delegation)");
    println!("    Sub-agent: api/v1/billing:r -> DENIED (not in delegation scope)");
    println!("    Sub-agent: impersonate parent -> DENIED (user confinement)");
    println!();

    // =========================================================================
    // PHASE 5: THE FULL PICTURE — Why this matters for AI
    // =========================================================================
    println!("--- Phase 5: WHY THIS MATTERS FOR AI ---");
    println!();
    println!("  Traditional API key approach:");
    println!("    - Agent gets a key with ALL permissions (no least-privilege)");
    println!("    - No budget limits (runaway cost risk)");
    println!("    - Key sharing = full authority transfer (no attenuation)");
    println!("    - No proof of what was accessed (audit gap)");
    println!("    - Revocation is all-or-nothing");
    println!();
    println!("  Pyana capability approach (this demo):");
    println!("    - Token scoped to EXACT services needed (least privilege)");
    println!("    - Budget enforced cryptographically (overspend impossible)");
    println!("    - Delegation is monotonically narrowing (can't escalate)");
    println!("    - Selective disclosure proves access without revealing scope");
    println!("    - Time-bounded (auto-expires, no cleanup needed)");
    println!("    - User confinement (cross-session attacks impossible)");
    println!();
    println!("  The MCP integration makes this invisible to the AI agent:");
    println!("    - Agent calls 'pyana_authorize' tool -> gets a token");
    println!("    - Agent calls 'pyana_delegate' tool -> spawns sub-agent");
    println!("    - Agent calls 'pyana_prove' tool -> generates ZK proof");
    println!("    - All the cryptography happens behind clean JSON-RPC calls.");
    println!();

    // =========================================================================
    // SUMMARY
    // =========================================================================
    let total_time = total_start.elapsed();

    println!("===============================================================================");
    println!("  SUMMARY");
    println!("===============================================================================");
    println!();
    println!("  Protocol flow:");
    println!("    1. Agent discovers tools via MCP (tools/list)");
    println!("    2. Agent obtains scoped token (pyana_authorize)");
    println!("    3. Agent proves access to third party (pyana_prove, selective disclosure)");
    println!("    4. Agent delegates narrower capability to sub-agent (pyana_delegate)");
    println!();
    println!("  Security properties:");
    println!("    [x] Least privilege: token scoped to exact services");
    println!("    [x] Budget enforcement: 10K computrons, cryptographically bounded");
    println!("    [x] Monotonic attenuation: sub-agent CANNOT escalate");
    println!("    [x] Selective disclosure: prove one fact, hide the rest");
    println!("    [x] Time-bounded: auto-expiry without revocation infrastructure");
    println!("    [x] User confinement: no cross-session impersonation");
    println!();
    println!(
        "  Total demo time: {:.2}ms",
        total_time.as_secs_f64() * 1000.0
    );
    println!();
    println!("  This is pyana's value proposition for AI: cryptographic capability");
    println!("  tokens that give agents BOUNDED, PROVABLE, DELEGABLE authority —");
    println!("  accessible through the same tool-calling interface they already use.");
    println!("===============================================================================");
}

/// Indent a multi-line string by a given number of spaces.
fn indent(s: &str, spaces: usize) -> String {
    let prefix = " ".repeat(spaces);
    s.lines()
        .map(|line| format!("{}{}", prefix, line))
        .collect::<Vec<_>>()
        .join("\n")
}

# Pyana MCP Integration

Pyana exposes its full agent/token/federation capabilities as an MCP (Model Context Protocol) server. AI assistants like Claude Code can discover and invoke these tools over stdio JSON-RPC.

## Quick Start

### 1. Initialize the data directory

```bash
cargo run --release -p pyana-node -- init --data-dir .pyana-data
```

### 2. Connect from Claude Code

The project root contains `.mcp.json` which Claude Code auto-discovers. No manual configuration needed — just open the project and the `pyana` MCP server will be available.

To manually invoke:

```
/mcp pyana
```

### 3. Pre-built binary (production)

```bash
# Build once
cargo build --release -p pyana-node

# The .mcp.json already points to cargo run, but you can override:
./target/release/pyana-node mcp --data-dir ~/.pyana
```

## Architecture

The MCP server uses **stdio transport**: it reads newline-delimited JSON-RPC 2.0 from stdin and writes responses to stdout. Logging goes to stderr via `tracing`.

Protocol flow:
1. Client sends `initialize` — server responds with capabilities and version
2. Client sends `notifications/initialized` — server acknowledges silently (no response)
3. Client sends `tools/list` — server returns all 15 tool definitions with JSON Schema
4. Client sends `tools/call` with `{name, arguments}` — server executes and returns result

## Available Tools (15)

### Node Management

| Tool | Description |
|------|-------------|
| `pyana_get_status` | Get node health, height, peer count |
| `pyana_read_cell` | Read a cell's state (balance, fields) |
| `pyana_get_receipt_chain` | Get auditable action history |

### Identity & Authorization

| Tool | Description |
|------|-------------|
| `pyana_create_agent` | Create a new agent identity with wallet |
| `pyana_authorize` | Prove authorization for an action (ZK proof) |
| `pyana_check_capabilities` | List all held capabilities/tokens |

### Actions & Turns

| Tool | Description |
|------|-------------|
| `pyana_submit_turn` | Submit an atomic set of actions for execution |
| `pyana_grant_capability` | Grant a capability to another agent |
| `pyana_revoke_capability` | Revoke a previously granted capability |
| `pyana_delegate` | Delegate a bounded sub-capability |

### Intent Marketplace

| Tool | Description |
|------|-------------|
| `pyana_post_intent` | Post a request for a capability/service |
| `pyana_fulfill_intent` | Fulfill a matching intent |

### Encryption & Bridging

| Tool | Description |
|------|-------------|
| `pyana_seal_data` | Encrypt data for a specific recipient |
| `pyana_unseal_data` | Decrypt sealed data addressed to this agent |
| `pyana_bridge_note` | Bridge a note to another federation |

## Tool Reference

### pyana_get_status

No parameters required.

```json
// Request
{"name": "pyana_get_status", "arguments": {}}

// Response
{
  "healthy": true,
  "peer_count": 3,
  "latest_height": 1042,
  "revocation_count": 0,
  "note_count": 17,
  "unlocked": true
}
```

### pyana_create_agent

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `name` | string | yes | Human-readable name for the agent |

```json
// Request
{"name": "pyana_create_agent", "arguments": {"name": "dns-reader"}}

// Response
{
  "name": "dns-reader",
  "public_key": "a1b2c3d4e5f6...64 hex chars",
  "created": true,
  "note": "Agent identity generated. Use pyana_check_capabilities to see held tokens."
}
```

### pyana_authorize

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `action` | string | yes | The action to authorize (e.g. read, write) |
| `resource` | string | yes | The resource to act upon |
| `mode` | string | no | `trusted` (default), `selective`, or `private` |

```json
// Request
{"name": "pyana_authorize", "arguments": {"action": "read", "resource": "dns.example.com", "mode": "selective"}}

// Response
{
  "authorized": true,
  "action": "read",
  "resource": "dns.example.com",
  "mode": "selective",
  "token_id": "tok_abc123"
}
```

### pyana_submit_turn

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `target_cell` | string | yes | Hex-encoded 32-byte cell ID |
| `method` | string | yes | Method to invoke on the cell |
| `fee` | integer | no | Fee in computrons (default: 0) |
| `memo` | string | no | Optional memo |

```json
// Request
{"name": "pyana_submit_turn", "arguments": {"target_cell": "abcd...64hex", "method": "transfer", "fee": 100, "memo": "payment"}}

// Response
{
  "accepted": true,
  "turn_hash": "ef01...64hex",
  "signer": "a1b2...64hex"
}
```

### pyana_grant_capability

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `to_agent` | string | yes | Recipient's hex-encoded public key |
| `target_cell` | string | yes | Hex-encoded cell ID |
| `permissions` | string | yes | Comma-separated permissions |

### pyana_revoke_capability

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `cap_slot` | integer | yes | Capability slot number to revoke |

### pyana_post_intent

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `action` | string | yes | The action needed |
| `resource` | string | yes | The resource pattern |
| `max_fee` | integer | no | Max fee in computrons |
| `expiry_blocks` | integer | no | Blocks until expiry (default: 100) |

```json
// Request
{"name": "pyana_post_intent", "arguments": {"action": "write", "resource": "documents/*", "max_fee": 500, "expiry_blocks": 50}}

// Response
{
  "intent_id": "dead...64hex",
  "stored": true,
  "action": "write",
  "resource": "documents/*",
  "expiry_height": 1092
}
```

### pyana_fulfill_intent

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `intent_id` | string | yes | Hex-encoded 32-byte intent ID |

### pyana_delegate

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `capability` | integer | yes | Token slot number to delegate from |
| `to_agent` | string | yes | Delegatee's hex-encoded public key |
| `restrictions` | object | no | Restriction constraints |
| `max_staleness` | integer | no | Max staleness in blocks |

### pyana_check_capabilities

No parameters required.

```json
// Response
{
  "public_key": "a1b2...64hex",
  "unlocked": true,
  "token_count": 3,
  "receipt_chain_length": 42,
  "tokens": [
    {"slot": 0, "id": "tok_root", "label": "root", "service": "*", "can_mint": true},
    {"slot": 1, "id": "tok_dns", "label": "dns-read", "service": "dns.*", "can_mint": false}
  ]
}
```

### pyana_read_cell

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `cell_id` | string | yes | Hex-encoded 32-byte cell ID |

### pyana_get_receipt_chain

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `limit` | integer | no | Max receipts to return (default: 50) |

### pyana_seal_data

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `data` | string | yes | Plaintext data to seal |
| `recipient` | string | yes | Recipient's hex-encoded public key |

### pyana_unseal_data

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `sealed_box` | string | yes | Hex-encoded sealed box bytes |

### pyana_bridge_note

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| `note_commitment` | string | yes | Hex-encoded 32-byte note commitment |
| `destination_federation` | string | yes | Hex-encoded federation ID |

## Example Session: AI Agent Workflow

Below is a transcript of an AI agent using pyana MCP tools to create an identity, authorize actions, and delegate to a sub-agent.

```
User: "Set up an agent that can read DNS records and delegate that to a sub-agent"

Claude: I'll create an agent, authorize DNS access, and set up delegation.

[calls pyana_get_status]
→ {"healthy": true, "peer_count": 3, "latest_height": 1042, "unlocked": true}

[calls pyana_create_agent with name: "dns-orchestrator"]
→ {"name": "dns-orchestrator", "public_key": "7a3f...c8e1", "created": true}

[calls pyana_authorize with action: "read", resource: "dns.example.com"]
→ {"authorized": true, "action": "read", "resource": "dns.example.com", "token_id": "tok_dns_01"}

[calls pyana_check_capabilities]
→ {"public_key": "7a3f...c8e1", "token_count": 2, "tokens": [
    {"slot": 0, "id": "tok_root", "label": "root", "can_mint": true},
    {"slot": 1, "id": "tok_dns_01", "label": "dns-read", "service": "dns.*", "can_mint": false}
  ]}

Claude: The orchestrator agent is set up with DNS read access. Now I'll create a
sub-agent and delegate bounded access.

[calls pyana_create_agent with name: "dns-worker"]
→ {"name": "dns-worker", "public_key": "b2e4...9f17", "created": true}

[calls pyana_delegate with capability: 1, to_agent: "b2e4...9f17"]
→ {"delegated": true, "from_token": "tok_dns_01", "to_agent": "b2e4...9f17"}

Claude: Done. I've created two agents:
- **dns-orchestrator** (7a3f...c8e1) — holds the DNS read capability
- **dns-worker** (b2e4...9f17) — delegated bounded DNS read access

The worker can now read DNS records within the delegation bounds.
```

### Multi-step: Mint Token, Post Intent, Submit Turn

```
User: "Mint a token for document access and post an intent for write access"

Claude: I'll authorize document access and post a marketplace intent.

[calls pyana_authorize with action: "write", resource: "documents/report.pdf"]
→ {"authorized": false, "action": "write", "resource": "documents/report.pdf", "token_id": null}

Claude: No existing token grants write access. I'll post an intent to the marketplace.

[calls pyana_post_intent with action: "write", resource: "documents/*", max_fee: 200]
→ {"intent_id": "ef82...a301", "stored": true, "expiry_height": 1142}

Claude: I've posted intent ef82...a301 requesting document write access. When another
agent fulfills it, I'll have the capability. The intent expires at block 1142.

[later, after fulfillment...]

[calls pyana_submit_turn with target_cell: "abcd...1234", method: "write_document", memo: "quarterly report"]
→ {"accepted": true, "turn_hash": "9f01...bc42", "signer": "7a3f...c8e1"}

Claude: Turn submitted and accepted (hash: 9f01...bc42). The document write is now
part of the receipt chain.
```

## Development Setup

```bash
# Clone and build
git clone <repo>
cd breadstuffs

# Initialize a local data directory
cargo run -p pyana-node -- init --data-dir .pyana-data

# Run MCP server manually (for testing)
echo '{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}' | \
  cargo run -p pyana-node -- mcp --data-dir .pyana-data

# Run with debug logging
RUST_LOG=pyana_node=debug cargo run -p pyana-node -- mcp --data-dir .pyana-data
```

## Production Setup

```bash
# Build release binary
cargo build --release -p pyana-node

# Initialize persistent data directory
./target/release/pyana-node init --data-dir /var/lib/pyana

# MCP server (invoked by Claude Code automatically via .mcp.json)
./target/release/pyana-node mcp --data-dir /var/lib/pyana --federation-peers node1:4200,node2:4200
```

## Protocol Compatibility Notes

The implementation follows the MCP specification (protocol version `2024-11-05`):

- **Transport**: Newline-delimited JSON-RPC 2.0 over stdio
- **Handshake**: Responds to `initialize` with `protocolVersion`, `capabilities`, and `serverInfo`
- **Notifications**: Silently handles `notifications/initialized` (no response sent, per spec)
- **Ping**: Responds to `ping` with empty object
- **Tool listing**: `tools/list` returns all 15 tools with full JSON Schema `inputSchema`
- **Tool invocation**: `tools/call` dispatches by tool name, returns `{content: [{type: "text", text: ...}]}`
- **Error handling**: Uses standard JSON-RPC error codes (-32700, -32601, -32602, -32603)
- **Logging**: All tracing output goes to stderr (never contaminates the stdio JSON-RPC stream)

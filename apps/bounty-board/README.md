# Pyana Bounty Board

A privacy-preserving bounty marketplace built on the pyana federation protocol.

Issuers post bounties with reward escrows and qualification requirements. Workers claim bounties by proving they meet the requirements **without revealing their identity** to the issuer. Payment is released atomically via conditional turns when work is approved.

## Privacy Model

The bounty board achieves the following privacy properties:

- **Worker anonymity**: Workers prove qualifications using zero-knowledge proofs (STARKs). The issuer never learns *which* federation member is working on their bounty until delivery.
- **Unlinkable claims**: Each claim uses a fresh blinded commitment (`hash(worker_key || randomness)`), so the same worker claiming multiple bounties cannot be linked across claims.
- **Selective disclosure**: For predicate-based qualifications (e.g., "reputation >= 5"), the worker proves the predicate holds without revealing the exact value.
- **Standing proofs via IVC**: Workers can prove they have completed N prior bounties using an IVC (incrementally verifiable computation) chain, without revealing *which* bounties.

## Qualification Proofs

When a bounty requires qualifications, the worker must provide a cryptographic proof:

| Qualification | What the worker proves | What stays hidden |
|---|---|---|
| `None` | Nothing required | N/A |
| `FederationMember` | "I am a member of this federation" (ring membership STARK) | Which specific member |
| `PredicateProof` | "My attribute >= threshold" (e.g., reputation >= 5) | The exact attribute value |
| `StandingProof` | "I have completed >= N bounties" (IVC chain) | Which specific bounties |

All verification is cryptographic (STARK-based). The bounty board never accepts unverified proofs -- if verification cannot be performed, it fails closed.

## Running Against the Devnet

### 1. Start the devnet

```bash
# Generate devnet genesis with 3 validators
pyana-node genesis --validators 3 --output /tmp/pyana-devnet

# Start node 0 (runs the HTTP API on port 8420 by default)
pyana-node run --data-dir /tmp/pyana-devnet --key-file node-0.key --gossip-port 9420 &
```

### 2. Start the bounty board

```bash
# Connects to node at http://127.0.0.1:8420 by default
cargo run -p pyana-bounty-board

# Or specify a different node URL
cargo run -p pyana-bounty-board -- --node-url http://127.0.0.1:8420

# Or provide an explicit federation root (skips node fetch)
cargo run -p pyana-bounty-board -- --federation-root <64-hex-chars>

```

The bounty board will:
1. Fetch the current attested federation root from the node on startup.
2. Start a background task that re-fetches the root every 30 seconds (configurable via `--sync-interval`).
3. Listen on `127.0.0.1:3030` (configurable via `--listen`).

### 3. Run the demo

```bash
./demo.sh
```

This creates a bounty, claims it, submits work, and approves payment -- all via curl.

## API Endpoints

### Bounty Lifecycle

| Method | Path | Description |
|--------|------|-------------|
| `POST` | `/bounties` | Create a new bounty |
| `GET` | `/bounties` | List bounties (with optional filters) |
| `POST` | `/bounties/{id}/claim` | Claim a bounty with qualification proof |
| `POST` | `/bounties/{id}/submit` | Submit completed work |
| `POST` | `/bounties/{id}/approve` | Issuer approves and triggers payment |
| `GET` | `/bounties/{id}/status` | Get detailed bounty status |

### Worker Endpoints

| Method | Path | Description |
|--------|------|-------------|
| `GET` | `/worker/bounties?commitment=<hex>` | List worker's active/completed bounties |

### Admin / Utility

| Method | Path | Description |
|--------|------|-------------|
| `GET` | `/health` | Health check with federation root, bounty counts, node status |
| `POST` | `/admin/height` | Advance simulated block height |
| `POST` | `/admin/expire` | Expire stale bounties past deadline |
| `POST` | `/admin/federation-root` | Manually set the federation root |

### Query Parameters for `GET /bounties`

- `tag` - Filter by tag (e.g., `?tag=rust`)
- `min_reward` - Minimum reward amount
- `max_reward` - Maximum reward amount
- `status` - Filter by status (`open`, `claimed`, `submitted`, `paid`, `expired`)

## Example: Creating a Bounty

```bash
curl -X POST http://127.0.0.1:3030/bounties \
  -H "Content-Type: application/json" \
  -d '{
    "title": "Implement Merkle proof helper",
    "description": "Write a helper for Merkle inclusion proofs.",
    "reward_amount": 5000,
    "reward_asset": 1,
    "deadline_height": 1000,
    "qualification": "None",
    "tags": ["rust", "crypto"],
    "issuer_cell": "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
    "reward_token": null
  }'
```

## Example: Claiming with a Qualification Proof

For bounties requiring `FederationMember`, the worker must provide a ring membership STARK:

```bash
curl -X POST http://127.0.0.1:3030/bounties/<id>/claim \
  -H "Content-Type: application/json" \
  -d '{
    "bounty_id": "<id>",
    "worker_commitment": [<32 bytes: hash(worker_key || randomness)>],
    "qualification_proof": [<STARK proof bytes>]
  }'
```

The proof is generated client-side using the `pyana-circuit` crate's ring membership prover. On the devnet, you can use the constraint prover for testing.

## Configuration

| Flag | Env Var | Default | Description |
|------|---------|---------|-------------|
| `--node-url` | `PYANA_NODE_URL` | `http://127.0.0.1:8420` | Node to fetch federation root from |
| `--federation-root` | `PYANA_FEDERATION_ROOT` | (fetched from node) | Explicit federation root (64 hex chars) |
| `--listen` | `PYANA_LISTEN` | `127.0.0.1:3030` | HTTP listen address |
| `--sync-interval` | `PYANA_SYNC_INTERVAL` | `30` | Root sync interval in seconds |

## Architecture

```
+-------------+     +--------------+     +-------------+
|   Issuer    |---->| Bounty Board |<----|   Worker    |
|  (cclerk)   |     |   (server)   |     |  (cclerk)   |
+-------------+     +--------------+     +-------------+
       |                    |                     |
  Post bounty         Verify proofs         Claim + prove
  (set escrow)       (STARK verify)       (ZK qualification)
                           |
                    +------+------+
                    |  Federation |
                    |    Node     |
                    +-------------+
                    (root sync every 30s)
```

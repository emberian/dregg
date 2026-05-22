# Pyana Federation Infrastructure on GitHub Actions

The pyana federation runs as persistent infrastructure on GitHub Actions free runners. Three federation nodes plus an intent pool service stay online continuously via staggered scheduled workflows that overlap, ensuring the network is always reachable.

## How It Works

### The Core Technique

GitHub Actions scheduled workflows can run for up to 6 hours. By scheduling each node to restart every 5 hours (with a 5h45m actual runtime), there is always overlap between the dying instance and the fresh one. State is persisted between runs via artifacts.

Since the node uses QUIC (quinn via pyana-net), the nodes are directly reachable on their runner's ephemeral public IPs. The discovery service maintains a coordination file so nodes can find each other across restarts.

### Schedule Stagger Logic

The three nodes are staggered by ~100 minutes so there's always at least one node up even during transitions:

| Node    | Schedule (UTC)                    | Cron Expression               |
|---------|-----------------------------------|-------------------------------|
| Node 1  | 0:00, 5:00, 10:00, 15:00, 20:00  | `0 */5 * * *`                 |
| Node 2  | 1:40, 6:40, 11:40, 16:40, 21:40  | `40 1,6,11,16,21 * * *`       |
| Node 3  | 3:20, 8:20, 13:20, 18:20, 23:20  | `20 3,8,13,18,23 * * *`       |
| Intent  | 2:50, 7:50, 12:50, 17:50, 22:50  | `50 2,7,12,17,22 * * *`       |

Each run lasts ~5h45m (timeout-minutes: 350), so a new instance starts before the old one dies.

### State Persistence

State chains between runs via GitHub Actions artifacts:

1. On startup: download `federation-node-N-state` artifact (continue-on-error for first run)
2. During runtime: state snapshot every 5 minutes (triggered by timer + SIGUSR1)
3. On shutdown: SIGTERM triggers final state save, then artifact upload
4. Artifact retention: 7 days (always re-uploaded to prevent expiry)

Persisted state includes:
- Latest attested root
- Known peers list
- Intent pool (for intent-service)
- Nullifier set (spent proofs)
- Snapshot counter (monotonic)

### Discovery

The `discovery.yml` workflow runs every 30 minutes and on `repository_dispatch` events from node workflows. It:

1. Downloads each node's state artifact
2. Reads the `discovery.json` file each node writes
3. Assembles a combined `site/discovery.json` with all active nodes
4. Commits to main (if changed) for GitHub Pages hosting
5. Uploads as `federation-discovery` artifact for cross-workflow access

Clients (like the browser extension) fetch `https://emberian.github.io/pyana/discovery.json` to find active federation nodes.

## Required Secrets

Configure these in the repository settings (Settings > Secrets and variables > Actions):

| Secret              | Description                                              | Format     |
|---------------------|----------------------------------------------------------|------------|
| `PYANA_NODE_1_KEY`  | Ed25519 private key for Node 1 (stable identity)         | 64 hex chars |
| `PYANA_NODE_2_KEY`  | Ed25519 private key for Node 2 (stable identity)         | 64 hex chars |
| `PYANA_NODE_3_KEY`  | Ed25519 private key for Node 3 (stable identity)         | 64 hex chars |
| `PYANA_ROOT_KEY`    | Federation root signing key (for token minting)          | 64 hex chars |

### Generating Keys

```bash
# Generate a random Ed25519 private key (64 hex chars = 32 bytes)
openssl rand -hex 32

# Or using the pyana toolchain (if available):
cargo run -p pyana-demo -- keygen
```

Each node's key is its stable identity across restarts. The root key authorizes token minting and should be kept especially secure.

## Adding a New Node

1. Generate a new Ed25519 key: `openssl rand -hex 32`
2. Add it as a repository secret: `PYANA_NODE_4_KEY`
3. Copy one of the existing `federation-node-N.yml` workflows
4. Change:
   - The schedule cron (pick a new stagger offset)
   - All references from `node-N` to `node-4`
   - The secret reference to `PYANA_NODE_4_KEY`
   - The concurrency group
5. Update `discovery.yml` to also download `federation-node-4-state`
6. Commit and push

## Architecture

```
+------------------+     +------------------+     +------------------+
|   Node 1 (GHA)  |<--->|   Node 2 (GHA)  |<--->|   Node 3 (GHA)  |
|  cron: */5 hrs   |     |  cron: +100min   |     |  cron: +200min   |
+--------+---------+     +--------+---------+     +--------+---------+
         |                         |                         |
         +------------+------------+------------+------------+
                      |                         |
              +-------v--------+        +-------v--------+
              | Intent Service |        |   Discovery    |
              |  (GHA, 5hrs)   |        |  (GHA, 30min)  |
              +-------+--------+        +-------+--------+
                      |                         |
                      |                   site/discovery.json
                      |                         |
              +-------v--------+        +-------v--------+
              |  Local Nodes   |        | Browser Ext.   |
              | (dev machines) |        | (fetch disco)  |
              +----------------+        +----------------+
```

## State File Format

### `state.json`

```json
{
  "latest_root": {
    "height": 42,
    "merkle_root": "abcd...",
    "attestations": [...]
  },
  "peers": [
    { "public_key": "...", "address": "1.2.3.4:4433", "registered_at": 1716163200 }
  ],
  "intent_pool": [],
  "nullifiers": [],
  "snapshot_counter": 123
}
```

### `discovery.json` (per-node)

```json
{
  "node_id": "quic-0.0.0.0:4433",
  "ticket": "pyana-quic://1.2.3.4:4433",
  "last_seen": "2026-05-20T12:00:00Z",
  "role": "node-1",
  "protocol": "quinn-quic",
  "addr": "0.0.0.0:4433"
}
```

### `site/discovery.json` (aggregated)

```json
{
  "federation": [
    { "node_id": "...", "ticket": "...", "last_seen": "...", "role": "node-1" },
    { "node_id": "...", "ticket": "...", "last_seen": "...", "role": "node-2" },
    { "node_id": "...", "ticket": "...", "last_seen": "...", "role": "node-3" }
  ],
  "intent_service": { "node_id": "...", "ticket": "...", "last_seen": "..." },
  "updated_at": "2026-05-20T12:30:00Z",
  "commit": "abc123def"
}
```

## Troubleshooting

### No state artifact on first run

Expected. The `continue-on-error: true` on the download step means the node bootstraps fresh. It will create its first state on the next snapshot.

### Artifact expired (>7 days without a run)

If all workflows stop for more than 7 days, artifacts expire. Nodes will bootstrap fresh. The federation is self-healing — a fresh node will sync state from peers on connection.

### Node can't reach peers

Runners get ephemeral public IPs. If all nodes restart simultaneously, they briefly can't find each other until discovery updates. The stagger schedule prevents this under normal operation.

### Build failures

The node must build on ubuntu-latest with nightly Rust. Check `node/Cargo.toml` dependencies and ensure workspace `[patch.crates-io]` entries don't conflict.

## Cost

All of this runs on GitHub Actions free tier:
- Public repos: 2,000 minutes/month (unlimited for public repos, actually)
- Each node: ~350 min/run * ~5 runs/day = ~1750 min/day
- For public repositories, scheduled workflows are free with no minute limits
- Only constraint: concurrent jobs (20 max for free tier — we use 4-5)

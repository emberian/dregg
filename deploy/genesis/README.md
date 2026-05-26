# Devnet Genesis Configuration

This directory contains the genesis state for the dregg devnet federation. It defines the initial accounts, deployed applications, route table, and validator set that every connecting node bootstraps from.

## Files

| File | Purpose |
|------|---------|
| `genesis.json` | Complete genesis state (accounts, cells, constitution, routes) |
| `accounts.json` | Pre-funded account manifest with roles and balances |
| `apps.json` | Deployed applications and their cell programs |
| `routes.json` | DFA route table (namespace access control) |
| `generate.sh` | Wrapper around `cargo run --release -p dregg-node -- genesis` |

## Generating Fresh Genesis State

```bash
cd deploy/genesis
./generate.sh          # first time
./generate.sh --force  # regenerate (wipes existing keys)
```

The script will:
1. Run `cargo run --release -p dregg-node -- genesis`
2. Generate Ed25519 validator keys (`node-{0,1,2}.key`)
3. Write validator env files (`node-{0,1,2}.env`)
4. Write canonical `genesis.json` and `.devnet`
5. Refuse to overwrite generated files unless `--force` is passed

### Prerequisites

- Rust toolchain (to build `dregg-node`)

### Generation Command

```bash
./deploy/genesis/generate.sh --force
```

## What's In genesis.json

### Accounts (10 pre-funded)

| Account | Balance | Role |
|---------|---------|------|
| alice | 10,000,000 | Power user (CDP, LP positions) |
| bob | 5,000,000 | Trader (open orderbook orders) |
| carol | 1,000,000 | Credential holder (3 VCs) |
| dave | 500,000 | New user (minimal state) |
| eve | 2,000,000 | Creator (NFT auctions) |
| faucet | 100,000,000 | Infrastructure (dispenses computrons) |
| treasury | 50,000,000 | Governance (DAO treasury, app owner) |
| relay | 10,000,000 | Infrastructure (store-and-forward) |
| nameservice | 5,000,000 | Infrastructure (name registry) |
| bridge-operator | 10,000,000 | Infrastructure (cross-chain bridge) |

### Constitution

- 3 validators (node-0, node-1, node-2)
- Threshold: 2 (BFT quorum)
- Timeout: 10 waves
- Epoch length: 100 waves
- Checkpoint interval: 10 waves

### Deployed Apps (as cells)

1. **Stablecoin** -- CDP manager + price oracle (2 cells)
2. **AMM** -- ETH/USDC and BTC/USDC constant-product pools (2 cells)
3. **Orderbook** -- Central limit order book (1 cell)
4. **Gallery** -- NFT auction house (1 cell)
5. **Nameservice** -- Human-readable name registry (1 cell)
6. **Governed Namespace** -- Root DFA delegation (1 cell)
7. **Identity Registry** -- Verifiable credential store (1 cell)

### Pre-configured State

- Alice: open CDP (1000 ETH collateral, 500 stablecoin debt)
- Alice: LP shares in ETH/USDC and BTC/USDC pools
- Bob: open limit orders (buy 10 @ 95, sell 5 @ 105)
- Carol: 3 issued credentials (age, country, org-membership)
- Eve: 2 NFTs listed for auction
- AMM pools: seeded with initial liquidity

### Route Table

```
/public/*   -> anonymous     (read)
/services/* -> members       (read, write)
/admin/*    -> admin         (read, write, configure)
/bridges/*  -> bridge-operator (read, write, relay)
/names/*    -> nameservice   (read, write, register)
/faucet/*   -> anonymous     (write, rate-limited)
/oracle/*   -> relay         (write)
```

## Deploying to Devnet

After generating:

```bash
# Copy genesis to the running node
scp genesis.json devnet.dregg.fg-goose.online:/opt/dregg-data/

# Restart the node to load new genesis
ssh devnet.dregg.fg-goose.online sudo systemctl restart dregg-gateway
```

Or use the automated deploy:

```bash
./deploy/aws/update.sh
```

## Security Notes

- `node-*.key` files are gitignored and must never be committed
- The checked-in `genesis.json` is a devnet artifact. Regenerate it before a fresh devnet deployment.
- Run `generate.sh` to produce canonical Ed25519 validator keys and genesis state
- These keys are for **devnet only** -- never reuse for production

# BE WARY

MOST OF THESE APPS ARE SIMPLY HELPING ME IRON OUT THE DESIGN

THEY ARE SHAPEFORMS I USED TO REVERSE-EXPLORE THE DESIGN SPACE

       THEY ARE MANY KNOWN ISSUES WITH ALL OF THEM

(except pyana-discord-bot. we love pyana-discord-bot.)

## apps/

Applications built on pyana. Each demonstrates real cryptographic properties — STARK proofs, Pedersen commitments, garbled circuits, ring membership, capability delegation. No mocks.

## Running

```bash
cargo run -p pyana-gallery          # :3000 — Art auctions
cargo run -p pyana-stablecoin       # :3050 — CDP stablecoin
cargo run -p pyana-amm              # :3051 — AMM/swap
cargo run -p pyana-identity         # :3052 — Verifiable credentials
cargo run -p pyana-orderbook        # :3053 — Trading
cargo run -p pyana-bounty-board     # :3001 — Bounties
cargo run -p compute-exchange       # :3002 — GPU marketplace
cargo run -p governed-namespace      # :3003 — Service mesh
cargo run -p pyana-discord-bot      # Discord bot (no HTTP)
```

Persistence: `--state-file path.json` or `PYANA_STATE_FILE` env.
Admin auth: `PYANA_ADMIN_TOKEN` env (Bearer header on `/admin/*`).

## The Apps

### `gallery/` — Privacy-Preserving Art Auctions

Sealed-bid, Vickrey, Dutch, and fully private auctions. The private Vickrey protocol hides bids (garbled circuits + OT), payment amount (Pedersen + equality proof), and winner identity (ring proof + stealth address). Settlement is atomic (TurnComposer). Provenance tracked as capability chain.

### `stablecoin/` — Collateralized Stablecoin

CDP lifecycle with STARK-enforced collateral ratio (14-column circuit). Oracle price via Ed25519-signed attestations. Liquidation engine. Deployed as CellProgram via ProgramRegistry.

### `amm/` — Constant-Product Market Maker

x*y=k invariant proven by STARK circuit (29 columns). Fee accumulation provably increases k. LP tokens via note model. Multi-hop routing. Slippage range-checked (16-bit decomposition).

### `orderbook/` — Verified Matching Engine

Price-time priority matching with STARK proof of fairness (MatchProofStarkAir). Commit-reveal anti-frontrunning. Pre-trade escrow (CreateObligation). Dark pool mode (Pedersen-committed amounts). Merkle state commitment.

### `lending/` — Decentralized Lending

Utilization-based interest rates. Health factor constraint circuit. Compound interest via iterated transition. Liquidation with bonus.

### `identity/` — Verifiable Credentials

Issue/present/revoke credentials. Selective disclosure. Predicate proofs ("age >= 18"). Non-revocation STARK proofs (sorted Merkle tree). Anonymous ring membership (BlindedMerkle — unlinkable presentations).

### `bounty-board/` — Federated Bounties

Real escrow (CreateObligation locks funds). Qualification via STARK membership/IVC proofs. Payment release via FulfillObligation. Federation root history for multi-validator coherence.

### `compute-exchange/` — GPU Marketplace

Dual escrow (payment + SLA bond). Commit-reveal fulfillment with 3-strike penalty. STARK delivery proof verification. Dispute resolution with timeout.

### `governed-namespace/` — Governed Service Mesh

DAO-controlled capability registry with DFA-based routing. Files stored as nameless writes (content-addressed, no indirection). Route table governed by constitutional threshold vote (propose → vote → atomic DFA swap). Service mesh: mount capabilities at named paths, discover by tags, resolve to sturdy refs (`pyana://` URIs). Auth levels: Anonymous, Member, Admin, Multisig(N) — classified by DFA. The directory is a programmable introduction service: registering = making your services discoverable to the DAO.

### `discord-bot/` — Devnet Interface (moved to toplevel `/discord-bot`)

19 slash commands: custodial cclerk, transfers, gallery bidding, DeFi (swap/lend/borrow), orderbook trading, credentials, federation status, block explorer (activity feed, lookups, watch lists), presence attestation (proof-of-online as dischargeable capability caveat).

**Note:** This crate has been promoted out of `apps/` to the toplevel
`/discord-bot` — it stands as a peer of `node/`, `sdk/`, etc. rather
than an app.

## Shared Architecture

- **axum** HTTP + WebSocket
- **Vanilla frontend** (HTML/JS/CSS, dark theme, extension bridge)
- **Real STARK proofs** (no mock feature)
- **Atomic persistence** (JSON snapshots, write-tmp-then-rename)
- **Admin auth** (Bearer token on mutation endpoints)

## Deployment

Behind Caddy at `devnet.pyana.fg-goose.online`:
- `/app/<name>/` — Static frontends
- `/<name>/*` — REST APIs
- `/ws` — WebSocket (gallery live events)
- `/metrics` — Prometheus

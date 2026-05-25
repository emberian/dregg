# App Promotion Strategy

## Which Demos Are Closest to Real Apps?

**Tier 1 (ready to promote):**
- `compute_marketplace` (817 LOC) — Full multi-party workflow with escrow, sealed-bid auction, atomic settlement. Has a clear user story and multiple distinct roles.
- `private_hiring` (662 LOC) — Complete cross-party predicate flow with intent posting, fulfillment, and conditional turn. Models a real marketplace interaction.
- `ai_agent_mcp_workflow` (503 LOC) — JSON-RPC MCP protocol simulation with cclerk, delegation, and selective disclosure. Closest to a real integration surface.

**Tier 2 (need structure but logic exists):**
- `rbac_datalog` (625 LOC) — Policy engine with STARK-proven decisions. Needs a request/response layer.
- `base_anonymous_credential` (493 LOC) — End-to-end anonymous presentation for on-chain verification. Needs a deployment target (contract + relayer).

## The Bounty-Board Pattern

The existing app at `apps/bounty-board/` (1727 LOC across 5 files) establishes the template:

| Layer | Implementation |
|-------|---------------|
| HTTP API | axum with typed JSON handlers |
| State | `tokio::sync::RwLock<HashMap>` (in-memory, persistence-ready) |
| Auth | Token verification via `pyana-sdk` + qualification proofs via `pyana-circuit` |
| Domain | Separate modules: `state.rs`, `payment.rs`, `qualification.rs` |
| Dependencies | `pyana-types`, `pyana-cell`, `pyana-turn`, `pyana-sdk`, `pyana-intent`, `token`, `pyana-circuit`, `pyana-store` |
| Frontend | None yet (API-first; frontend would live in a `site/` sibling) |

**Pattern summary:** axum REST API + in-memory state + domain logic split into modules + circuit proofs for privacy-sensitive operations.

## Proposed Apps

### 1. `apps/policy-gateway` — Enterprise Access Control

**Audience:** Enterprise (RBAC, audit, compliance)
**Promotes:** `rbac_datalog` + `progressive_disclosure`

An HTTP policy decision point. Services POST authorization requests; the gateway evaluates Datalog, returns allow/deny, optionally attaches a STARK proof for audit. Supports three disclosure modes per request.

- **LOC:** ~1200 (gateway logic exists in the two demos; add axum routes + policy storage)
- **Crates:** `pyana-trace`, `pyana-circuit`, `pyana-sdk`, `token`
- **ZK:** Yes (Fully Private mode proves decisions without revealing policy internals)
- **Demo:** CLI (`curl` against local server) + optional web dashboard showing policy graph

### 2. `apps/agent-hub` — AI Agent Capability Server

**Audience:** AI/agent developers
**Promotes:** `ai_agent_mcp_workflow` + `sub_agent_spawn` + `delegation_swarm`

An MCP-compatible server that provisions capability tokens to AI agents, tracks delegation chains, enforces budget gates, and handles sub-agent spawning with attenuated authority.

- **LOC:** ~1500 (MCP JSON-RPC handler + cclerk registry + delegation tracker)
- **Crates:** `pyana-sdk`, `pyana-turn`, `pyana-cell`, `token`, `pyana-bridge`
- **ZK:** No (delegation + budget enforcement works with just token attenuation)
- **Demo:** Both (CLI agent driver + web UI showing live delegation tree)

### 3. `apps/anon-credential-gate` — Privacy-Preserving Verification

**Audience:** Privacy / identity
**Promotes:** `base_anonymous_credential` + `anonymous_credit_check`

A verification endpoint where users prove predicates (age >= 18, credit >= 720) without revealing values. Supports committed thresholds (verifier's threshold also stays hidden) and ring membership (unlinkable presentations).

- **LOC:** ~1000 (proof generation is already built; add HTTP presentation endpoint + verifier)
- **Crates:** `pyana-circuit` (committed_threshold, ring membership), `pyana-bridge`, `token`
- **ZK:** Yes (core value proposition; STARK proofs for every verification)
- **Demo:** Web (browser submits proof, gets pass/fail badge; zero server-side PII)

### 4. `apps/compute-exchange` — Decentralized Job Marketplace

**Audience:** Infrastructure / developer
**Promotes:** `compute_marketplace` + `private_orderbook`

Sealed-bid compute auctions with atomic multi-party settlement. Providers stake via note commitments, clients escrow via cell programs, settlement is a single atomic turn across 6+ cells.

- **LOC:** ~1800 (the 817-line demo has most logic; add HTTP layer, bid storage, reveal scheduler)
- **Crates:** `pyana-cell`, `pyana-turn`, `pyana-intent`, `pyana-commit`, `pyana-circuit`, `token`
- **ZK:** Yes (sealed bids use nullifier commitments; settlement proofs for disputes)
- **Demo:** CLI (provider/client binaries) + web dashboard showing auction state

### 5. `apps/hiring-board` — Private Talent Matching

**Audience:** Enterprise + Privacy crossover
**Promotes:** `private_hiring` + `intent_lifecycle`

Companies post job intents with predicate requirements. Candidates prove qualifications (experience, skills, salary range) via ZK predicates without revealing exact values. Match happens through the intent pool with commit-reveal anti-frontrunning.

- **LOC:** ~1400 (private_hiring is 662 LOC of pure logic; add intent pool HTTP layer + match notifications)
- **Crates:** `pyana-intent`, `pyana-circuit`, `pyana-sdk`, `pyana-turn`, `token`
- **ZK:** Yes (predicate proofs for every qualification check)
- **Demo:** Web (two-sided UI: company posts requirements, candidate proves qualifications)

## Summary Table

| App | Audience | LOC | Needs ZK | Demo Surface |
|-----|----------|-----|----------|--------------|
| policy-gateway | Enterprise | ~1200 | Yes | CLI + Web |
| agent-hub | AI/Agent | ~1500 | No | CLI + Web |
| anon-credential-gate | Privacy | ~1000 | Yes | Web |
| compute-exchange | Infrastructure | ~1800 | Yes | CLI + Web |
| hiring-board | Enterprise+Privacy | ~1400 | Yes | Web |

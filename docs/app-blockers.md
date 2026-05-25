# App Blockers and Fixes

## 1. policy-gateway (Enterprise RBAC + Progressive Disclosure)

| Blocker | Crate | Effort |
|---------|-------|--------|
| No `DisclosureMode` enum exposed at SDK top-level; developers must manually construct `DisclosureSpec` with raw fact indices. Need a `PolicyDecisionRequest -> PolicyDecisionResponse` helper that maps three modes (Full/Selective/Private) to proof generation. | sdk | 2 days |
| Datalog evaluation (`verify_token_datalog`) lives in `token` crate and returns `DatalogVerifyResult`, but there is no way to pipe that result into a STARK proof of the decision. The circuit proves predicates, not Datalog conclusions. Need a `DatalogDecisionAir` or an adapter that reduces a Datalog result to a predicate proof. | circuit + token | 1 week |
| No policy storage abstraction. Bounty-board used in-memory `HashMap`; policy-gateway needs persistent policy rules (Datalog programs). `store/` only stores attestation roots and revocations, not arbitrary domain data. | store | 2 days |

## 2. agent-hub (AI Agent MCP Server + Delegation)

| Blocker | Crate | Effort |
|---------|-------|--------|
| MCP server (`node/src/mcp.rs`) has `pyana_delegate` tool, but it requires the cclerk to already hold the token in a numbered slot. No MCP tool for multi-hop delegation tracking or delegation-tree queries (e.g., "show all sub-agents spawned from token X"). | node | 3 days |
| `AgentRuntime::spawn_sub_agent` works locally but has no wire-level counterpart. A remote agent cannot request a sub-agent spawn over MCP/JSON-RPC; the hub would need a `pyana_spawn_sub_agent` tool with budget propagation. | sdk + node | 3 days |
| Budget gate (`BudgetSlice`) is set per-runtime but not enforced cross-turn. If a sub-agent submits two turns, there is no persistent budget ledger deducting from the slice. Need a `BudgetLedger` that persists across turns. | turn | 3 days |
| No built-in delegation revocation propagation to sub-agents. When a parent revokes, children continue operating until their token naturally expires or a revocation check is performed. Need an event/push mechanism. | sdk + wire | 2 days |

## 3. anon-credential-gate (Privacy -- Committed Threshold Proofs)

| Blocker | Crate | Effort |
|---------|-------|--------|
| SDK exposes `prove_committed_threshold` on `AgentCipherclerk` but no corresponding `verify_committed_threshold` at the SDK level. Verifier must drop to `pyana_circuit::committed_threshold::verify(...)` directly. Need a top-level SDK verification function. | sdk | 4 hours |
| Ring membership proof (`authorize_anonymously`) requires the cclerk to have federation membership, but there is no SDK helper to construct the federation Merkle tree for a verifier endpoint. A gate service needs `build_federation_tree(member_keys) -> root` exposed. | sdk or bridge | 1 day |
| No HTTP-layer proof serialization format documented. `WirePresentationProof` goes over TCP (wire crate), but the credential gate wants to accept proofs over REST/JSON. Need a `serde_json`-compatible proof wrapper or base64 encoding convention. | bridge | 1 day |

## 4. compute-exchange (Sealed-Bid + Atomic Settlement)

| Blocker | Crate | Effort |
|---------|-------|--------|
| Sealed bids in the demo use `NullifierSet` for commit-uniqueness, but there is no timed-reveal scheduler. The demo manually reveals; a real app needs a `RevealPhase` struct with timeout enforcement (reject reveals after deadline, slash no-reveals). | intent or new crate | 3 days |
| No escrow primitive. The demo simulates escrow by asserting cell balances; there is no `Effect::Escrow` or `Effect::ConditionalRelease` in the turn executor. Settlement requires a two-phase lock pattern that must be hand-rolled from `BridgeLock`. | turn + cell | 1 week |
| Multi-party atomic settlement (6+ cells) needs transaction coordination. `TurnExecutor` processes a single turn atomically, but orchestrating conditional cross-party turns (provider commits only if client commits) has no built-in support. Need a `ConditionalTurnBundle` or similar. | turn | 1 week |
| No dispute resolution mechanism. If a provider delivers bad compute, there is no on-chain challenge/response protocol. Would need a `DisputeAir` or a timeout-based refund path in the settlement logic. | circuit + turn | 2 weeks |

## 5. hiring-board (Enterprise+Privacy -- Predicate Matching via Intents)

| Blocker | Crate | Effort |
|---------|-------|--------|
| Intent system works without a network (`IntentPool` is in-process), but `receive_intent_checked` requires a valid `StakeProof` with a known Merkle root for gossip-propagated intents. For a hosted hiring board that accepts intents over HTTP, there is no "trusted relay" mode that skips stake verification. | intent | 1 day |
| Predicate fulfillment via MCP is blocked: `tool_fulfill_intent` explicitly errors if predicates are required, telling the caller to "use the full fulfillment API". The full API (`execute_fulfillment_flow`) exists but requires pre-computed `PredicateProof` objects -- no SDK-level `fulfill_with_predicates(intent, my_attributes)` convenience. | sdk + intent | 3 days |
| No notification/webhook system. When a candidate fulfills an intent, the company needs to be notified. The gossip layer (`IntentPool.pending_matches()`) is pull-based and in-process only. Need an event stream (WebSocket or SSE) for match notifications. | node or new | 2 days |
| Anti-frontrunning (`FulfillmentCommitment` / `FulfillmentReveal` in gossip.rs) exists but is not wired into the fulfillment execution flow. `execute_fulfillment_flow` does not check whether a commitment was registered before accepting a reveal. | intent | 1 day |

## Cross-Cutting Gaps

| Blocker | Crate | Effort |
|---------|-------|--------|
| `cargo doc` output exists only for `cross_node_auth` and `hints` binaries -- not for the SDK or core crates. No published rustdoc for app developers. | all | 2 days |
| Wire protocol client (`SiloClient`) requires raw TCP. No HTTP/WebSocket client for browser or serverless environments. The WASM crate exists but does not re-export `SiloClient`. | wire + wasm | 1 week |
| Node startup is undocumented. `node/src/main.rs` exists but there is no `--dev` or single-command local federation bootstrap. Developers must manually configure peers, genesis, and store paths. | node | 2 days |
| Discharge gateway is a separate binary with no Docker compose or integration test showing how apps connect to it. The SDK has `obtain_discharge` but no example of wiring it into an axum app. | discharge-gateway + docs | 1 day |

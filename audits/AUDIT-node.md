# Node Security Audit — `node/src/*`

**Auditor model:** Claude Opus 4.7
**Date:** 2026-05-23
**Scope:** `node/src/{main,api,mcp,state,blocklace_sync,gossip,ws,routing_table,metrics,multi_group,relay_service,genesis,blocklace_sync_checkpoint}.rs` (13 files, ~13.5k LOC), cross-referenced with `sdk/`, `coord/`, `turn/`, `cell/`, `storage/`.

## Verdict: **NEEDS-WORK** (with one **CRITICAL** finding)

The node has a clear architecture, defensive scaffolding (rate limiting, body size limits, CORS, Argon2id passphrase hashing, BLAKE3 bearer-token KDF with constant-time compare, persistent replay-prevention sets), and demonstrates good cryptographic hygiene where it tries. **But** four independent classes of trust-boundary failure are present, and they compound. The single highest-impact finding is **F-CRIT-1**: in initial-setup mode the node allows the *first* HTTP caller to set the wallet passphrase with no loopback check, which on a node started with `--bind 0.0.0.0` becomes a remote takeover. There is no CRITICAL break of the documented signing/proof model, but the **enrollment-time identity** of the operator is not protected against network attackers, which subsumes any later auth.

---

## Summary

The node is a single-process Axum daemon hosting (a) an `AgentWallet` (the operator's identity & signing key), (b) a `Ledger` of cells, (c) a `PersistentStore` (redb), (d) a blocklace consensus engine, (e) an HTTP API (~50 routes), (f) a WebSocket gossip channel, (g) an MCP stdio JSON-RPC server (37 tools), and optionally (h) a relay operator service on a separate port. All of the above share **one wallet, one signing key, one ledger** in a `tokio::sync::RwLock<NodeStateInner>`.

The trust model is implicitly *operator-only*: localhost is treated as the operator. CORS restricts browsers to localhost; `--bind 127.0.0.1` is the default. But several endpoints bypass that assumption: (1) the WebSocket loopback check is correct *only* in pre-passphrase setup mode but the equivalent HTTP path is not gated; (2) `auto_approve_joins = true` is unconditionally on in blocklace consensus, allowing any peer who can deliver a gossip block to join the federation; (3) the relay subcommand binds `0.0.0.0` and accepts authority claims by hex string with no signature; (4) several "protected" endpoints (`post_create_from_factory`, `post_make_sovereign`, `post_peer_exchange`, every `pyana_*` MCP tool) take cell-id-shaped arguments and act on them on behalf of the wallet without ownership verification beyond "are you authenticated to this node."

The node's *cryptographic* code is largely fine: turn signatures are verified before execution in `execute_finalized_turn` (line 1172), ed25519 signatures gate `register_cell` / `deregister_cell` / `update_commitment`, vote signatures are pre-verified before coordinator dispatch (line 2310-2321), conditional-proof nullifiers are persisted at use time, the discharge gateway persists its `issued_set` immediately. Where the node fails is in *authorization* (who is allowed to ask for what), not authentication of cryptographic artifacts.

---

## Findings by severity

### P0 — CRITICAL

**F-CRIT-1. Pre-passphrase HTTP API accepts any caller as wallet operator.** `node/src/api.rs:646-650` — `require_auth` middleware short-circuits with `Ok(next.run(req))` when `bearer_seed` is `None`. The two passphrase endpoints (`/wallet/unlock`, `/wallet/set-passphrase`) are in `public_routes` and not gated by `require_auth` at all. Combined with `--bind 0.0.0.0` (an operator-supportable mode that prints only a `tracing::warn!`), any network attacker who reaches the port before the operator runs `set-passphrase` can call `POST /wallet/set-passphrase` to choose the passphrase, then derive the bearer token themselves. **The WebSocket handler does enforce this check (`ws.rs:133`); the HTTP handler does not.** Fix: in `require_auth` *and* in the two passphrase POST handlers, reject non-loopback `ConnectInfo` when `bearer_seed.is_none()`. The faucet path is already devnet-only-by-flag; this is a stronger constraint.

**F-CRIT-2. Blocklace consensus auto-approves all join proposals.** `node/src/blocklace_sync.rs:659` — `auto_approve_joins: true` is hardcoded, with an in-source `TODO(production)`. Any node that publishes a `MembershipAction::Join` block on the gossip topic causes every existing participant to cast an `Approve` vote. Combined with the BFT threshold `(n*2/3)+1`, a single attacker can flip an N-node federation into an (N+1)-node federation that includes them — they then receive shares of any threshold-decryption ceremonies and participate in tau ordering. Fix: gate on the `.devnet` marker (the file is already created by `genesis.rs:157`), or behind a CLI flag (`--auto-approve-joins`), defaulting to false.

### P1 — should fix

**F-P1-1. Relay service has no caller authentication on any privileged endpoint.** `node/src/relay_service.rs:441-486` — `handle_drain` accepts `?owner=<hex>` and returns all messages addressed to that owner. There is no signature, no token, no ownership proof. The comment "in production, derived from auth token" is a TODO. `handle_unsubscribe` (line 345) and `handle_subscribe` (line 279) are similar. The service binds `0.0.0.0` unconditionally (line 619-622). **Anyone on the network can drain anyone's inbox.** Fix: require an Ed25519 signature over `(owner, max, nonce, current_height)` whose pubkey matches `owner`; reject otherwise.

**F-P1-2. `post_create_from_factory` and `post_make_sovereign` perform privileged ledger writes with no ownership check.** `api.rs:3141-3179` and `api.rs:3193-3222`. Both are in `protected_routes` (bearer-auth required), but the bearer token represents the *node's operator* — not the cell's owner. An authenticated operator-tier caller can call `post_make_sovereign` with *any* `cell_id` and turn it sovereign with a commitment of `BLAKE3(cell_id)`, overwriting whatever the actual cell state was. The same caller can call `post_create_from_factory` to register provenance for a cell they don't own. Fix: require an Ed25519 signature whose pubkey equals the cell's `public_key` field on the ledger.

**F-P1-3. `post_submit_turn` signs an attacker-supplied `agent: CellId` with the node's wallet.** `api.rs:1118-1138`. The endpoint accepts `agent` in the request body and uses it as `turn.agent`, then signs with `s.wallet.sign_turn(&turn)`. The node operator's signing key is bound to a turn whose agent field may be a cell the operator doesn't actually control. The downstream `execute_finalized_turn` requires the signature to match `signed_turn.signer` (which is `wallet.public_key()`), so the agent field is *informational* relative to the signature — but the cell `agent` being targeted is what the executor uses for capability lookup. A confused-deputy attack: caller supplies `agent = some_cell_id_belonging_to_victim`, the executor finds the victim's c-list under that ID, and the wallet's signature is what attests authority. This contrasts with the MCP path (`mcp.rs:889-891`) which correctly derives `agent_cell_id = CellId::derive_raw(&wallet.public_key().0, &[0u8;32])`. Fix: HTTP `post_submit_turn` should mirror MCP and derive `agent` from the wallet's pubkey, not accept it from the body.

**F-P1-4. `post_atomic_proposal` populates participant key map with bogus keys.** `api.rs:2205-2208` — `let participant_keys = participants.iter().map(|&id| (id, id)).collect();`. This sets every participant's verifying key to their *cell ID*, with an explicit comment "In production: lookup real public keys." The `Coordinator::receive_vote` later verifies vote signatures against this map. The vote handler (line 2310-2321) *also* does a defense-in-depth sig verify using `voter` as the verifying key — same bug. If `cell_id != ed25519_pubkey`, signatures will fail unconditionally; if they happen to be equal (sovereign cells where `cell_id = pubkey`), the protocol works but is brittle. Fix: read participant pubkeys from `known_federation_keys` or a passed-in `participant_pubkeys` field on the request.

**F-P1-5. `tool_create_agent` discards the freshly-generated wallet.** `mcp.rs:790-813` — generates a new `AgentWallet::new()`, prints its public key, and the wallet is dropped immediately. There is no persistence, no association with the user/name, and the returned `public_key` is meaningless. This is a *correctness* bug rather than a security bug, but an LLM acting on the response would believe it has minted an agent it can later reference. Fix: persist the wallet in a sub-agent table, or remove the tool.

**F-P1-6. `tool_seal_data` derives X25519 secret from sealing wallet's symmetric key via a `recipient_pubkey` interpreted as X25519, but the sender uses an ephemeral key — mismatched protocol.** `mcp.rs:1664-1693`. The sender generates a fresh X25519 secret and DHs with `recipient_pubkey` *interpreted as X25519*. The recipient (`tool_unseal_data:1734`) derives X25519 secret from `wallet.derive_symmetric_key("pyana-mcp-seal-x25519-v1")` — a key derived from the wallet's identity. So the sender must use the recipient's *X25519 public key derived the same way* to make this work, but `tool_seal_data`'s `recipient` parameter is documented as "hex-encoded public key of the intended recipient" with no specification of *which* key. If a caller passes the recipient's Ed25519 public key (the natural thing to do), sealing and unsealing will never agree. Fix: document explicitly that `recipient` must be the recipient's `derive_symmetric_key("pyana-mcp-seal-x25519-v1")` *public* counterpart, or — better — implement Ed25519-to-X25519 conversion at both ends.

**F-P1-7. `post_bearer_auth` uses `known_federation_keys.first()` as federation ID.** `api.rs:3316-3321`. Picks the first key out of a `HashSet`-derived `Vec` ordering, which is unstable. The federation ID used for delegation signature verification can vary across runs. Fix: federation ID should be a separate config item (`silo_id` or `federation_id`).

**F-P1-8. `tool_exercise_bearer_cap` constructs `BearerCapProof` with `permissions: Signature` hardcoded** (`mcp.rs:2180`) regardless of the user-supplied `permissions_str`. The `_perm_level` variable (line 2074, leading underscore) is parsed but unused — the actual `BearerCapProof.permissions` is always `Signature`. Fix: use `_perm_level` (rename and use it).

**F-P1-9. `tool_unseal_data` operates over `String::from_utf8_lossy` of decrypted plaintext** (`mcp.rs:1748`). If the sealed payload is binary, the lossy conversion silently mangles it. The MCP response declares the operation succeeded with a corrupted `data` field. Fix: return base64-encoded bytes when the plaintext is not valid UTF-8, or split into `seal_text` and `seal_bytes` tools.

**F-P1-10. `multi_group.rs::join_group` and `leave_group` have no caller authentication.** While they are not directly exposed via HTTP, they are `pub fn` on the module and any future endpoint wiring them up inherits no guard. Fix: gate behind explicit authorization.

### P2 — would-be-nice

**F-P2-1. `post_atomic_proposal` accepts `max budget = u64::MAX`.** `api.rs:2215` — coordinator is created with `u64::MAX` and "actual gate applied at execution time" is the comment, but no execution-time gate is referenced. Fix: clamp to a sensible per-proposal budget.

**F-P2-2. `post_resolve_conditional` reads `trusted_executor_keys` from `known_federation_keys` (api.rs:2002).** This is correct, but conditional proofs whose freshness window is bound to the federation root age can be replayed across `set_federation_keys` events. Fix: include federation epoch in the `condition` hash.

**F-P2-3. Discharge gateway evaluator hardcoded to `ProofRequiredEvaluator` (api.rs:3076).** No way to configure additional evaluators (rate limits, attestations) through the HTTP API. Fine for now; flag for future extensibility.

**F-P2-4. Several `.expect("SignedTurn serialization")` (api.rs:1191, mcp.rs:940/1075/1159/1495).** `postcard::to_stdvec` on a typed `SignedTurn` "should not fail", but a misbehaving custom serde impl on a field could panic the executor task. Low risk but worth propagating.

**F-P2-5. `node/src/api.rs:702` — `Response::builder()...body(empty()).unwrap()` on the CORS preflight path.** Unwrap is safe (constant inputs) but spells out a pattern.

**F-P2-6. `nibble` and `hex_decode` are duplicated** across `api.rs`, `mcp.rs`, `blocklace_sync.rs`, `relay_service.rs`. Each has slightly different error types. Consolidate into one helper.

**F-P2-7. `tool_get_status` requires `s.unlocked` (mcp.rs:763)** but the HTTP `/status` does not. The HTTP one is fine; the MCP one is over-strict (status should be readable while locked).

**F-P2-8. `post_intent` recomputes `Intent::new` (api.rs:1444) to verify content-addressed ID.** Good, but `Intent::new` calls `getrandom` in some constructions. If the constructor is non-deterministic for some fields, this check is wrong. Verify `Intent::new` is purely a function of its inputs.

**F-P2-9. `routing_table::mark_verified` (line 117-127) ignores its `authorizing_turn` parameter** and marks *all* entries for the cell as verified. Comment acknowledges this. Real possibility of marking a malicious route as verified. Fix: store `authorizing_turn` in `RouteEntry` and verify by it.

**F-P2-10. The MCP tool `pyana_prove_sovereign_turn` uses `initial_state = CellState::new(1000, 0)` hardcoded** (`mcp.rs:2525`) as the prover's initial state. The proof is therefore a proof about a state that doesn't exist on-ledger. A naïve consumer of the response would believe a real cell transition was proven.

**F-P2-11. `tool_compress_history` builds `new_roots` as `initial_root_u32.wrapping_add((i+1) as u32)`** (`mcp.rs:2019`). The compressed proof is over fictitious roots, not the actual cell history. Same naming-vs-behavior concern.

**F-P2-12. PIR query path (`api.rs:2749-2782`) acquires a write lock** on `state.write().await` to read/cache the index. Multiple concurrent PIR queries serialize through one write lock. Could DoS via traffic. Fix: use a separate `Mutex<Option<IntentIndex>>` cached field on the read path.

**F-P2-13. `post_peer_exchange` does not actually do any peer exchange** (api.rs:3351-3384). Only logs and returns. Aspirational naming.

**F-P2-14. `tool_deploy_factory` does NOT register the factory anywhere** (`mcp.rs:2264-2331`). Returns a `descriptor_hash` and the `_descriptor_hash_copy` line acknowledges nothing is persisted. The HTTP endpoint `post_deploy_program` does persist into `program_registry`, but the MCP analog does not — inconsistent semantics.

**F-P2-15. `tool_propose_membership` does not actually submit the proposal** (`mcp.rs:3044-3104`) — builds a `MembershipProposal` and computes a hash, but never feeds it to the constitution manager or creates a `Payload::MembershipVote` block.

**F-P2-16. `MAX_BODY_SIZE = 1 MB` (api.rs:784)** is global. The `post_deploy_program` endpoint accepts a hex-encoded `CircuitDescriptor` — at 1 MB that's a 512 KB binary descriptor. Postcard deserialize of a malformed `CircuitDescriptor` could be slow. The `pyana_dsl_runtime::CellProgram::new(descriptor, version)` and `program_registry.deploy(program)` are not audited here.

### P3 — notes

**F-P3-1. `node.key` file: 32 raw bytes, mode 0o600.** Good. Not encrypted at rest. Operators who lose disk control lose the wallet.

**F-P3-2. `expand_path` only handles `~/` (main.rs:600).** No environment variable expansion. Fine.

**F-P3-3. `tracing::warn!` for `--bind 0.0.0.0`** (main.rs:510) is the only friction against the F-CRIT-1 trap. Promote to an explicit confirmation or a separate `--unsafe-bind` flag.

**F-P3-4. `participant_keys` map for atomic proposals: `(id, id)` identity mapping** is documented in source as a placeholder. See F-P1-4.

**F-P3-5. `MAX_NODE_INTENT_POOL = 10_000`** (api.rs:778) is a reasonable cap. PIR row width grows linearly though.

**F-P3-6. `solo` mode finalizes every block immediately.** Trivially correct in solo (you're the only consensus); but it means a node started in solo mode that *later* gains peers has already locally finalized blocks the peers haven't seen. Federation upgrade path needs care.

**F-P3-7. `event_log: VecDeque` with `MAX_EVENT_LOG = 1000`** is fine. No persistence — restart loses recent events.

---

## API / Endpoint inventory

### HTTP routes (`api.rs::router`)

Trust classes: **public** = no auth; **operator** = require_auth bearer (== passphrase-derived); **devnet** = enabled only with CLI flag.

| Route | Method | Trust class | Notes |
|---|---|---|---|
| `/status`, `/health`, `/api/node/{status,health}` | GET | public | ok |
| `/federation/roots`, `/api/blocks` | GET | public | ok |
| `/api/cells`, `/api/cell/{id}` | GET | public | exposes balances of all cells |
| `/api/intents`, `/intents` (GET) | GET | public/operator | intent pool listing |
| `/api/conditionals`, `/turn/pending` | GET | public/operator | |
| `/api/discharge` | POST | public | requires unlock; gateway verifies ticket |
| `/api/events` | GET | public | ring buffer events |
| `/checkpoint/latest`, `/checkpoint/{h}` | GET | public | ok |
| `/api/blocklace/checkpoint` | GET | public | ok |
| `/pir/info`, `/pir/query` | GET/POST | public | **F-P2-12** write-lock contention |
| `/wallet/unlock`, `/wallet/set-passphrase` | POST | public | **F-CRIT-1** |
| `/api/faucet` | POST | devnet | ok |
| `/ws` | GET upgrade | operator (loopback in setup) | ok |
| `/wallet`, `/wallet/{tokens,receipts}` | GET | operator | ok |
| `/wallet/{authorize,mint,attenuate}` | POST | operator | ok |
| `/intents` (POST), `/intents/encrypted`, `/intents/fulfill` | POST | operator | ok |
| `/turn/submit`, `/api/turns/submit` | POST | operator | **F-P1-3** signs attacker-supplied agent |
| `/turn/{fast-path,certificate}` | POST | operator | ok (verifies cert) |
| `/turn/{submit,resolve}-conditional` | POST | operator | ok |
| `/turn/atomic[/vote\|/{id}\|/evaluate]` | POST/GET | operator | **F-P1-4** participant keys map |
| `/cell/{id}` | GET | operator | ok |
| `/cells/{register,deregister,update-commitment}` | POST | operator | ed25519-sig-verified |
| `/cells/create-from-factory`, `/cells/make-sovereign` | POST | operator | **F-P1-2** no ownership check |
| `/programs/deploy` | POST | operator | postcard deserialize, no size cap beyond 1 MB body |
| `/proofs/compose` | POST | operator | ok (informational) |
| `/turns/bearer-auth`, `/api/turns/bearer-auth` | POST | operator | **F-P1-7** federation ID picked from first key |
| `/turns/peer-exchange` | POST | operator | **F-P2-13** no-op |
| `/queues/*` | various | operator | placeholder implementations |
| `/metrics` | GET | public | Prometheus; intentional |

### MCP tools (`mcp.rs::tool_definitions`)

All MCP tools require `s.unlocked` and run over `stdio` of the `pyana-node mcp` subcommand. **The MCP transport itself is unauthenticated** — anyone with shell access to the user's stdin/stdout can drive every tool. This is the standard MCP model (the calling LLM is the operator), but it means an MCP-tool-callable wallet on a shared machine is fully compromised.

| Tool | Action | Notes |
|---|---|---|
| `pyana_get_status` | read | ok |
| `pyana_create_agent` | mints+drops wallet | **F-P1-5** |
| `pyana_authorize` | local verify | ok |
| `pyana_submit_turn` | signs+executes | ok (derives agent from wallet pk) |
| `pyana_grant_capability` | signs+executes | uses wallet's own cell as `from` |
| `pyana_revoke_capability` | signs+executes | ok |
| `pyana_post_intent` | mints intent | random commitment_id, no stake |
| `pyana_fulfill_intent` | settles payment | rejects intents with predicate reqs |
| `pyana_delegate` | mints DelegatedToken | ok |
| `pyana_check_capabilities` | read | ok |
| `pyana_read_cell` | read | always returns balance=null (placeholder) |
| `pyana_get_receipt_chain` | read | ok |
| `pyana_seal_data` / `pyana_unseal_data` | XChaCha20-Poly1305 | **F-P1-6**, **F-P1-9** |
| `pyana_bridge_note` | signs+executes BridgeLock | empty spending_proof |
| `pyana_make_sovereign` | ledger write | initial commitment = BLAKE3(cell_id) — placeholder |
| `pyana_peer_exchange` | informational | no actual on-ledger effect |
| `pyana_compress_history` | proof gen | **F-P2-11** uses synthetic roots |
| `pyana_create_bearer_cap` / `pyana_exercise_bearer_cap` | signed delegation | **F-P1-8** hardcoded perm |
| `pyana_deploy_factory` | informational | **F-P2-14** does not persist |
| `pyana_create_from_factory` | ledger write | no ownership check |
| `pyana_verify_provenance` | read | ok |
| `pyana_prove_sovereign_turn` / `pyana_verify_sovereign_proof` | STARK | **F-P2-10** synthetic initial state |
| `pyana_create_stealth_address` | mints address | XOR-based, documented as simplified |
| `pyana_private_transfer` | signs+executes NoteCreate | BLAKE3 "Pedersen" (documented) |
| `pyana_encrypt_intent` | SSE-encrypted intent | ok |
| `pyana_prove_predicate` | proof gen | ok |
| `pyana_compose_proofs` | informational | hashes inputs only |
| `pyana_get_blocklace_status`, `pyana_get_constitution` | read | ok |
| `pyana_propose_membership` | informational | **F-P2-15** does not submit |
| `pyana_check_resource_budget` / `pyana_debit_shared_resource` | budget ops | ok |
| `pyana_list_auctions` / `pyana_place_bid` | reads intent pool / mints intent | ok |

### Relay routes (`relay_service.rs::relay_router`, binds `0.0.0.0`)

| Route | Method | Auth | Notes |
|---|---|---|---|
| `/relay/status` | GET | none | public read |
| `/relay/subscribe` | POST | none | **F-P1-1** no owner-sig check |
| `/relay/unsubscribe` | DELETE | none | **F-P1-1** |
| `/relay/send/{dest}` | POST | none | accepts deposit, OK |
| `/relay/drain` | GET | none (!) | **F-P1-1** drains anyone's inbox |
| `/relay/inbox/{id}/status` | GET | none | public read |
| `/relay/proof/{msg_id}` | GET | none | public read |

---

## Cross-cutting patterns

1. **Authority bound to operator process, not to per-resource keys.** The HTTP API treats "you have the bearer token" as "you are the wallet." This conflates two trust levels: operator-level (start/stop, set passphrase, configure peers) vs. per-cell-owner (mint, attenuate, transfer this specific cell). For multi-tenant or app-framework integration this design is dangerous; for single-operator devnet it is acceptable. **F-CRIT-1**, **F-P1-2**, **F-P1-3** are all instances.

2. **Aspirational MCP tools.** `pyana_deploy_factory`, `pyana_propose_membership`, `pyana_create_agent`, `pyana_peer_exchange` all return success responses for operations that have no on-ledger effect. An LLM acting on these believes it has changed state that it has not. (Parallel to AUDIT-sdk-rest.md's bool-returning verifiers, but worse — these *return success*.)

3. **Hardcoded devnet defaults shipping as production-ready.** `auto_approve_joins: true`, the `0.0.0.0` bind option, the unauthenticated relay drain — each is annotated with a `TODO`/`in production this would be...` comment but not gated by `cfg(any(test, feature = "devnet"))` or runtime check. The `.devnet` marker exists; nothing checks it after `main.rs:341` (which only emits a warning).

4. **Placeholder participant-key mappings.** Both `post_atomic_proposal` (F-P1-4) and `post_bearer_auth` (F-P1-7) approximate "the real federation map" with whatever's at hand. Atomic proposals rely on this for vote-signature verification; bearer auth uses it for federation_id binding.

5. **Postcard deserialization without size bounds.** `post_deploy_program` decodes hex up to 1 MB and `postcard::from_bytes` into `CircuitDescriptor`. The descriptor's safety bounds are checked by `ProgramRegistry::deploy`, but the deserialize itself could be slow or memory-heavy for adversarial inputs.

6. **`.expect()` and `.unwrap()` on `postcard` / `serde_json` serialization in hot paths.** Many — see F-P2-4. Not directly exploitable but a fault-tolerance concern.

7. **Verification-vs-truth: register endpoints.** `post_register_cell` requires an ed25519 signature where `cell_id == pubkey`, but `post_create_from_factory` and `post_make_sovereign` (the operator's "shortcuts") do not. There is no consistent rule.

---

## Open questions for the user

1. **F-CRIT-1 fix scope**: should the loopback-only guard apply to *all* `public_routes` during pre-passphrase setup, or only to the passphrase-set endpoints? I recommend all of `public_routes` minus `/status` and `/health` (these need to be reachable for monitoring even pre-setup).

2. **F-CRIT-2 fix**: should `auto_approve_joins` be (a) tied to the `.devnet` marker file, (b) tied to a separate CLI flag, or (c) removed entirely (require human approval via gossip-published vote)? Option (a) matches existing patterns.

3. **F-P1-3 (`post_submit_turn` agent spoofing)**: is the HTTP-level `agent` parameter expected to support multi-cell operators (one wallet operating multiple cells), or should it always equal the wallet's derived cell id? If multi-cell, the body should include a signature from each agent's private key.

4. **Relay service**: is the relay subcommand intended to be deployed by third parties (operator-as-a-service), or is it for the same operator who runs the node? If third-party, **F-P1-1** is critical (P0). If same-operator, the relay should bind to localhost by default.

5. **MCP transport**: is `pyana-node mcp` intended to be driven only by the local operator's LLM client, or could it be wrapped in a remote MCP gateway? If remote, the MCP needs Bearer auth on the JSON-RPC envelope.

6. **Atomic proposal participant keys**: who provides the per-participant Ed25519 pubkeys at proposal time? Currently the request only carries the *cell IDs*. Suggest adding `participant_pubkeys: Vec<String>` to `AtomicProposalRequest`.

7. The audit found no exploitable break of the wallet/turn signing model that the SDK audits documented. Are there specific attack scenarios on the node (e.g., bridge-takeover, federation-impersonation) you want adversarial tests constructed for?

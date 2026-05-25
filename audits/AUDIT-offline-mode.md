# AUDIT: Offline mode in pyana

**Question:** Can pyana operate fully offline? What can happen offline, what requires consensus, and how does the offline/online seam work?

**Read-only audit.** Tracing call sites in `sdk/src/cipherclerk.rs`, `sdk/src/runtime.rs`, `turn/src/executor.rs`, `turn/src/fast_path.rs`, `turn/src/turn.rs`, `turn/src/verify.rs`, `federation/src/solo.rs`, `federation/src/lib.rs`, `node/src/api.rs`, `node/src/blocklace_sync.rs`, `captp/src/store_forward.rs`, `captp/src/session.rs`, `sdk/src/captp_client.rs`.

---

## TL;DR

Pyana is offline-first in its primitives and online-only in its safety claims.

- **Crypto/proof construction.** The `AgentCipherclerk` and `AgentRuntime` paths that build, sign, prove and apply turns are **pure, synchronous, in-process functions.** They reach the network only via three explicitly `async + #[cfg(feature = "federation-client")]` methods that ship as opt-in REST clients.
- **Execution.** `TurnExecutor::execute` is `fn execute(&self, turn: &Turn, ledger: &mut Ledger) -> TurnResult` — no I/O, no peer lookup, no clock except what the caller injects via `set_timestamp`. It will happily commit turns and emit receipts against a local in-memory `Ledger`.
- **Consensus.** Safety against forks/equivocation/double-spend lives one layer up in `pyana-blocklace` (Cordial Miners DAG + tau ordering), `pyana-federation` (BFT quorum, attested roots), and `node/src/blocklace_sync.rs` (gossip + replay).
- **Bridge.** The offline → online transition has **two distinct seams**:
  1. **Same-node-rejoin** (the node was running but partitioned): `FederationMode::Solo` produces `Finality::Tentative` receipts and a `NullifierLog` that peers replay-and-validate when the partition heals (`federation/src/solo.rs`).
  2. **Independent cclerk → federation** (the cclerk was never connected): the cclerk just hangs on to its in-memory ledger and receipt chain. To make it externally visible, *some* online node must accept and re-execute the turn through the blocklace path (`node/src/api.rs::post_submit_turn` → `gossip_turn` → `execute_finalized_turn`).
- **The non-answer.** What pyana does **not** have today is a "pure offline cclerk that accumulates receipts then atomically posts them to consensus." The cipherclerk's offline receipts are *self-attested only*; nothing in the on-chain path consumes a cclerk-generated `TurnReceipt`. The chain rebuilds its own receipt by re-executing the turn.

---

## 1. AgentCipherclerk offline: signing, building, proving

**Result: a cclerk can sign turns, build authorization proofs, and produce STARK proofs entirely offline. None of the canonical "build & sign" entry points are `async` or touch the network.**

### 1a. Cipherclerk API surface — local vs network

In `sdk/src/cipherclerk.rs`, network reachability is fully visible as Rust syntax. Searching for every method whose body talks to a peer:

```
$ grep -n "federation-client\|reqwest::" sdk/src/cipherclerk.rs
5134:    #[cfg(feature = "federation-client")]
5137:        node_url: &str,                # register_with_federation
5161:        let client = reqwest::Client::new();
5206:    #[cfg(feature = "federation-client")]
5207:    pub async fn deregister_from_federation(&self, node_url: &str)
5219:        let client = reqwest::Client::new();
5266:    #[cfg(feature = "federation-client")]
5267:    pub async fn deploy_program(&self, node_url: &str, ...)
5282:    let client = reqwest::Client::new();
```

**Exactly three** cclerk methods make network calls, and all three are feature-gated:
- `register_with_federation` (cclerk → `/cells/register`)
- `deregister_from_federation` (cclerk → `/cells/deregister`)
- `deploy_program` (cclerk → `/programs/deploy`)

Everything else is pure compute. The "core dance" methods we care about are all **synchronous (`pub fn`, not `pub async fn`)**:

| Method | Behaviour |
|---|---|
| `sign_turn` (cipherclerk.rs:2361) | Hashes the turn locally, calls `signing_key.sign(&turn_bytes)`, returns a `SignedTurn`. |
| `sign_action` (cipherclerk.rs:2403) | Builds the canonical signing message via `TurnExecutor::compute_signing_message`, signs it, returns an `Action`. |
| `make_action` (cipherclerk.rs:2440) | Constructs an unsigned `Action` and sends it through `sign_action`. |
| `make_turn` / `make_turn_for` (cipherclerk.rs:2475, 2480) | Wraps an `Action` in a `CallTree`/`CallForest`/`Turn`. Reads `self.receipt_chain.last()` to populate `previous_receipt_hash`. |
| `build_authorized_turn` (cipherclerk.rs:2548) | Builds an `AuthRequest`, calls `self.authorize(...)` → STARK proof bytes, wraps into a `Turn`, calls `sign_turn`. |
| `prove_authorization` (cipherclerk.rs:2882) | Calls `pyana_bridge::BridgePresentationBuilder::prove(...)` — pure prover. |
| `prove_authorization_with_issuer_key` (cipherclerk.rs:2957) | Same, with out-of-band issuer key for attenuated tokens. |
| `prove_program`, `prove_predicate`, `prove_arithmetic`, `prove_relational`, `prove_committed_threshold`, `prove_for_intent_predicates`, `prove_with_chain` | All synchronous, all delegate to in-process `pyana-circuit` provers. |
| `mint_token`, `attenuate`, `delegate*`, `receive_signed_delegation`, `receive_local_delegation` | Macaroon caveat operations, BLAKE3-keyed; pure. |
| `append_receipt`, `verify_own_chain`, `current_state_commitment` | Local receipt-chain bookkeeping. |

### 1b. Trace: one signed turn, end to end, offline

The lowest-level offline construction site is `AgentRuntime::execute` in `sdk/src/runtime.rs:215-307`. Note that `AgentRuntime` owns its own private `Arc<Mutex<Ledger>>` (line 129) and `TurnExecutor` (line 130), constructed in `AgentRuntime::new`:

```rust
let mut ledger = Ledger::new();
let agent_cell = Cell::with_balance(public_key.0, ..., 1_000_000);  // 1M computrons
ledger.insert_cell(agent_cell).expect(...);
let executor = TurnExecutor::new(ComputronCosts::default_costs());
```

The signed-turn dance (runtime.rs:215-307):

1. Build unsigned `Action` (no auth).
2. Compute the canonical signing message: `TurnExecutor::compute_signing_message(&action_unsigned, &self.executor.local_federation_id)`.
3. `self.cclerk.read()...sign_bytes(&message)` — local signing.
4. Reattach `Authorization::from_sig_bytes(sig.0)` to the action.
5. Acquire `self.ledger.lock()`.
6. Allocate a nonce from `self.nonce`.
7. Read `self.cclerk.read()...receipt_head().map(|r| r.receipt_hash())` to populate `previous_receipt_hash`.
8. Build the `Turn { agent, nonce, call_forest, fee: 10_000, ... }`. **The fee 10_000 referenced in the demo is hardcoded right here at runtime.rs:276.**
9. `self.executor.execute(&turn, &mut ledger)` — see §2.
10. On `TurnResult::Committed { receipt, .. }`, `self.cclerk.write()...append_receipt(receipt.clone())`.

**External calls: zero.** No `await`, no socket, no DNS, no peer query. The agent's cclerk, its 1M computron starting balance, the executor, the ledger, and the receipt chain are all in one process.

### 1c. Sub-agent / domain-separated cipherclerks

`AgentCipherclerk::derive_sub_agent(index)` (cipherclerk.rs:1024) performs HKDF-style derivation from the parent's secret key bytes. Pure compute. The result is an independent `AgentCipherclerk` whose receipt chain starts at zero.

---

## 2. TurnExecutor: what is a receipt offline?

`turn/src/executor.rs`. The single execution entry point is

```rust
pub fn execute(&self, turn: &Turn, ledger: &mut Ledger) -> TurnResult   // line 2598
```

This function:
- **never `await`s** (the entire `TurnExecutor` impl block is sync — no `async fn` anywhere on it),
- **never reads a clock** beyond `self.current_timestamp` and `self.block_height`, which are caller-set,
- **never asks a peer for anything** — there is no `&self.network`, `&self.peers`, etc. The struct has none.

### 2a. What goes into the receipt

`TurnReceipt` (turn/src/turn.rs:362-409) is locally determined:

```rust
pub struct TurnReceipt {
    turn_hash, forest_hash,
    pre_state_hash, post_state_hash,    // == ledger.root() before / after
    timestamp, effects_hash,
    computrons_used, action_count,
    previous_receipt_hash,              // chain link
    agent,
    federation_id,                      // == self.local_federation_id
    routing_directives, introduction_exports, derivation_records, emitted_events,
    executor_signature,                 // Option<Vec<u8>> — see below
    finality,                           // Final | Tentative
}
```

All inputs are functions of the in-memory `Ledger`, the `Turn`, the executor's configured `local_federation_id` / `current_timestamp` / `block_height`, and (optionally) the executor's signing key. None require quorum.

### 2b. What is the "meaning" of an offline receipt?

**Pyana's receipts have no consensus-derived ground truth baked into them.** A receipt with `finality: Final` produced by an offline `TurnExecutor` looks structurally identical to a receipt produced by a quorum of validators. The chain doesn't sign the receipt — at most one executor does.

Specifically:
- `executor_signature` is only populated when `executor_signing_key` is set (executor.rs:621, 762-776). The default `TurnExecutor::new()` leaves it `None`. The runtime in `sdk/src/runtime.rs:123` constructs the executor with `TurnExecutor::new(...)` and never sets a key. **Therefore, every receipt the SDK's `AgentRuntime` produces has `executor_signature = None`.**
- `finality` defaults to `Final` (turn.rs:355-358). The runtime's executor leaves it at `Final`. **The cipherclerk's offline-produced receipts claim full finality.**
- The chain `verify_receipt_chain` (verify.rs:117-177) checks only that (a) the chain is non-empty, (b) it has a genesis, (c) hashes link, (d) `pre_state_hash` of N+1 == `post_state_hash` of N, (e) all receipts belong to the same agent. It does **not** require any executor signature. `verify_receipt_chain_with_keys` (verify.rs:245) verifies signatures *when present*, but silently passes receipts where `executor_signature` is `None`.

**So an offline `AgentCipherclerk`'s receipt chain is a self-attested record that:**
1. The agent (who has the keys) believed they ran these turns in this order;
2. State transitioned according to *their* local ledger;
3. Nobody else has signed off on it.

This is fine for personal bookkeeping and proof of *intent*. It is not, by itself, sufficient evidence to anyone else that the turn happened in the real world.

### 2c. Tentative vs Final

`turn/src/turn.rs:341-358` defines `Finality::{Final, Tentative}`. The node API path (`node/src/api.rs:1183-1197`) flips a freshly-executed receipt to `Tentative` when `s.federation_mode == FederationMode::Solo` *and* records the turn hash into `solo.nullifier_log`. That's the only place where finality is downgraded based on consensus mode.

The cipherclerk's `AgentRuntime` path does not know about federation modes and produces `Final` receipts unconditionally. This is arguably a bug — a cclerk that's never been online cannot honestly stamp `Final` — but it's the current code.

---

## 3. Receipt-chain semantics for two offline parties

**Short answer: a receipt Alice produces about her own cell is binding only on Alice's chain. Alice cannot produce a receipt that touches Bob's state without Bob's signature.**

The structural reasons:

1. **`Turn.agent` is one CellId.** A turn has a single `agent` field (`turn.rs`), and `TurnExecutor::execute` performs all auth checks against that agent's cell at line 2620:

   ```rust
   let agent_cell = match ledger.get(&turn.agent) {...}
   if agent_cell.state.nonce() != turn.nonce { reject }
   if agent_cell.state.balance() < turn.fee { reject }
   ```

   The fee must come from `agent`'s balance. So Alice cannot construct a turn against Bob's cell that pays from Bob's balance unless she holds Bob's signing key.

2. **Authorization is verified, not implicit.** `Action.authorization` is checked inside `execute_tree` — signatures against the action's signing message, STARK proofs against the action's `authorization_proof` slot, or bearer-cap traversal. The executor verifies these before applying effects. None of these checks are skipped by the SDK path.

3. **Effects that touch other cells require explicit authorization.** Cross-cell transfers (`Effect::Transfer { from, to, amount }`) require that the agent has authority over `from`; `Effect::Grant`, `Introduce`, `SpawnWithDelegation` need derivation records etc. The executor enforces this even in pure-local mode.

### 3a. Can Alice fork her own chain?

**Yes — and pyana relies on consensus to expose the fork, not to prevent its construction.**

`AgentCipherclerk::reset_receipt_chain()` doesn't exist as a public method, but `append_receipt` does (cipherclerk.rs:1775). Alice can:

1. Run turn T1 → receipt R1 (linked to genesis None).
2. Walk back her in-memory ledger to the pre-T1 state.
3. Run turn T1' (different action) at nonce 0 → receipt R1' (also linked to genesis None).
4. Keep both R1 and R1' in two private chains.

Nothing in `sdk/src/cipherclerk.rs` or `turn/src/executor.rs` detects this — the executor's `last_receipt_hash` map (executor.rs:594-607) only enforces forward consistency per `(executor, agent)` pair. Two separate `TurnExecutor` instances cannot see each other's history. (One can be the local in-memory runtime executor; another can be the node's executor.)

**The defense against forks is at consensus time:**

- The fast-path lock table (`turn/src/fast_path.rs:203-247`) keyed on `(CellId, nonce)` ensures at most one fast-path turn per cell+nonce gets a quorum (`process_fast_path_lock` line 322 + `assemble_certificate` line 430 + `effective_quorum_threshold` from `federation/src/solo.rs:80`).
- The blocklace's equivocation detection (`pyana_blocklace::finality::BlockError::Equivocation`, surfaced in `node/src/blocklace_sync.rs:803-823`) auto-evicts creators who sign two blocks at the same `(creator, seq)`. The constitution manager records the proof.
- The `NullifierLog` (federation/src/solo.rs:114) gives a sequenced, signed record of nullifier insertions; rejoin replays it (`validate_remote_entries`, line 187) and rejects on conflict.

**Net effect:** offline Alice can _construct_ contradictory receipts, but the moment two contradictory turns hit consensus from different replicas, one is rejected. The receipt chain alone is insufficient evidence of uniqueness; it must be combined with consensus-level uniqueness commitment.

---

## 4. Federation handoff: offline → online

`federation/src/solo.rs` and `node/src/blocklace_sync.rs` are the two relevant files. The protocol is **block-replay**, not "submit a batch of receipts."

### 4a. The block-replay contract

The unit of sync is a `pyana_blocklace::finality::Block`, not a `TurnReceipt`. From `node/src/blocklace_sync.rs`:

```rust
pub enum BlocklaceGossipMessage {
    Push(Vec<Block>),                        // I think you need these
    Pull(Vec<BlockId>),                      // I'm missing these
    PullResponse(Vec<Block>),
    Frontier(HashMap<[u8; 32], BlockId>),    // lightweight catch-up
    CheckpointAvailable { height, checkpoint_hash },
}
```

A block contains a `Payload::Turn(Vec<u8>)` — the postcard-encoded `SignedTurn`. When a peer comes online and receives blocks, the flow is:

1. `handle_push` (blocklace_sync.rs:777) calls `lace.receive_block(block)`. The blocklace itself rejects equivocation, missing predecessors, and bad signatures.
2. `poll_finalized_blocks` (line 238) runs `tau(...)` for the multi-party case (or a topological sort in solo) and returns the newly ordered blocks.
3. `execute_finalized_turn` (line 1157) deserializes the `SignedTurn`, verifies the signature, then **re-executes** the turn through a fresh `TurnExecutor` against the local ledger.

**The peer's view of "what really happened" is the result of re-executing the turn against the same deterministic executor — not the receipt the originating cclerk stored.** Cipherclerk-produced receipts never cross the wire as canonical evidence; the turn does, and consensus generates the canonical receipt at the destination.

### 4b. Solo-mode rejoin

`federation/src/solo.rs` describes the rejoin contract:

```text
When peers come back online:
1. They receive the solo node's signed nullifier log
2. They validate each entry (no double-spends, valid signatures)
3. Tentative receipts are promoted to Final if no conflicts
4. The federation upgrades back to Full mode
```

`SoloConsensusState::detect_peers` (line 318) flips mode `Solo → Full` and `effective_threshold` from 1 to `quorum_threshold(n)`. The nullifier-log merge is `NullifierLog::validate_remote_entries` (line 187) + `merge_validated` (line 220). On conflict, `NullifierConflict { nullifier }` is returned — but **the code in this module only describes the protocol; the actual promotion of `Tentative → Final` receipts is not visibly implemented anywhere in `node/src/blocklace_sync.rs` that I can find**. Searching for `Finality::Tentative` shows only one consumer: the API path that *creates* tentative receipts in `api.rs:1186`. There is no `... = Finality::Final` rewrite path. **Open question; see §9.**

### 4c. The cipherclerk's "I was offline, here are my turns" path

There is no batch-sync method on `AgentCipherclerk`. The cclerk does not expose `replay_chain_to_node`, `submit_all_pending`, or similar. The intended workflow today appears to be:

- Cipherclerk builds + signs + (optionally) proves each turn offline.
- Cipherclerk keeps the `SignedTurn` blobs (in memory; persistence is the caller's job).
- When the cclerk is online again, the caller submits each `SignedTurn` to a node's HTTP `/turn/submit` endpoint one by one.
- Each submission goes through the blocklace path (`api.rs:post_submit_turn` → `gossip_turn` → `execute_finalized_turn`).
- The node, on each submission, re-executes the turn against *its* ledger and produces *its* receipt. If the offline ledger has diverged from the federation's view, all subsequent submissions fail (nonce mismatch, balance shortfall, etc.).

Note that `previous_receipt_hash` is populated by the cclerk from its own local chain, but the node's executor (`turn/src/executor.rs:843-864 check_previous_receipt_hash`) compares it against the node's `last_receipt_hash` map. **If the offline cipherclerk's chain has receipts the node has never seen, the node will reject the next turn with `TurnError::ReceiptChainMismatch`.** This is `EXECUTOR-HONESTY-AUDIT.md` Stage 9 R-4 territory.

This is the fundamental seam:

```
Cipherclerk's local ledger                Node's ledger (consensus-derived)
       |                                       |
       | offline turns appended                |
       v                                       |
   chain head = h_offline                  chain head = h_online (older)
       |                                       |
       +-------- submit turns ---------------->|
                                               |
                  WALLET'S TURNS RE-EXECUTED   |
                  on node's ledger, generating |
                  fresh receipts that DO NOT   |
                  match the cipherclerk's h_offline |
```

**The cipherclerk's locally-built receipt chain is not the chain that ends up on consensus.** They share `turn_hash`, `pre_state_hash`, `post_state_hash` *if* the underlying state genuinely agrees, but the receipts themselves are different objects (different `timestamp`, different `executor_signature`, possibly different `federation_id`).

This is a real design tension. See §9 open questions.

---

## 5. Computron fees: local or federation-mediated?

**Fees are debited locally and re-debited at the node. Distribution requires the federation.**

### 5a. Where the fee is debited

`turn/src/executor.rs:2731-2734`:

```rust
let agent = ledger.get_mut(&turn.agent).unwrap();
agent.state.set_balance(agent.state.balance() - turn.fee);
agent.state.increment_nonce();
```

This is Phase 1, "never rolled back" (line 2727 comment). It happens in any `TurnExecutor`, offline or online.

### 5b. Where the fee goes

`executor.rs:2816-2825` (proof-carrying path; the normal path is the same):

```rust
let proposer_share = turn.fee / 2;
let treasury_share = turn.fee * 3 / 10;
// 20% burned (no recipient)
proposer.state.set_balance(proposer.state.balance() + proposer_share);   // if proposer_cell set
treasury.state.set_balance(treasury.state.balance() + treasury_share);   // if treasury_cell set
```

Critical: `proposer_cell` and `treasury_cell` are `Option<CellId>` (executor.rs:542-544). If `None`, the corresponding share is burned. The cipherclerk's `AgentRuntime` never sets either (`runtime.rs:123` constructs the executor with `TurnExecutor::new(...)` and stops). **Offline, 100% of the fee is burned.** That's not a bug per se — there's no federation to pay — but it means the cipherclerk's local ledger drains by `turn.fee` per turn against itself only.

### 5c. Who pays?

The agent. Always the agent. `turn.fee` must be ≤ `agent_cell.state.balance()` (executor.rs:2643). There is no concept of "node pays" or "delegated fee payer" anywhere in the executor.

### 5d. Computron creation: epoch minting requires federation

`turn/src/economics.rs::EpochMinter::maybe_mint` (line 205) credits the **treasury cell** when an epoch boundary is crossed. The treasury cell is a federation-configured cell (executor.rs:893). Offline, no minting happens (and no treasury to mint to). Long-term offline-only operation in a cclerk leads to a deflationary drain to zero.

### 5e. The fee=10_000 demo number

`sdk/src/runtime.rs:276` hardcodes `fee: 10_000` in `AgentRuntime::execute`. The two-AI handoff demo runs through this path; the demo also funds Alice and Bob with `1_000_000` (`runtime.rs:117`). 100 turns = empty cclerk.

---

## 6. Queues: local effects on a federated structure

`Effect::QueueAllocate`, `QueueEnqueue`, `QueueDequeue`, `QueueAtomicTx`.

In `sdk/src/cipherclerk.rs:5506-5800`, the cipherclerk's queue methods are all `pub fn` (not async), and each returns a `Turn` ready for submission. The cclerk builds the turn locally; no network. The `previous_receipt_hash` is set from `self.receipt_chain.last()`.

The actual queue state lives in `TurnExecutor::queue_program_registry` (executor.rs:593) and is mutated when `apply_effect` processes `Effect::QueueAllocate / QueueEnqueue / QueueDequeue / QueueAtomicTx`. Because the registry hangs off the executor instance, **each executor has its own queue state.** The cipherclerk's `AgentRuntime` executor has a separate queue registry from the node's executor.

**Implication:** if Alice enqueues a message offline against her local executor, that enqueue exists *only* in her local ledger. For the rest of the federation to see it, the turn must be submitted to a node and re-executed; the node's executor materialises its own queue state. As with everything else, the wire-level shared state is "the turn," not "the queue."

Queue programs (`Cargo.toml` shows `queue_programs.rs` in `turn/src/`) bind validation programs to queue IDs by VK hash. The VK hash itself is computed offline; deploying it to the federation requires `cclerk.deploy_program(node_url, ...)` (cipherclerk.rs:5267, network-only).

---

## 7. The contract between offline ops and consensus

Distilled from the above:

| Operation | Offline-doable | Globally-visible-without-consensus | Notes |
|---|---|---|---|
| Mint / attenuate / delegate a macaroon token | yes | yes (recipient verifies bearer signature locally) | Capability creation is fundamentally local. |
| Sign a turn | yes | no | Signature is necessary but not sufficient. |
| Produce a STARK authorization proof | yes | yes (anyone can verify) | The proof is independent of consensus. |
| Apply a turn to your own ledger | yes | no | Local replay only. |
| Produce a receipt (`Final` or `Tentative`) | yes | no | Receipt is self-attested unless executor signs and verifier trusts the executor key. |
| Bind a turn to the receipt chain head | yes | maybe | Chain head must agree with consensus-side history or next turn is rejected. |
| Pay a fee (debit own balance) | yes | no | Local debit. Federation share is burned when offline. |
| Receive a fee share (as proposer or treasury) | no | n/a | Requires being the federation's configured proposer/treasury and the executor to be running with those set. |
| Allocate / enqueue / dequeue a queue entry | yes locally | no | Queue state is per-executor; only consensus-side execution makes it shared. |
| Create a sovereign cell (`make_sovereign`) | yes | requires `register_with_federation` to be online-visible | cipherclerk.rs:4269. |
| Send a CapTP message to a peer | not really | no — see §8 | The wire-delivery seam is unimplemented (see audit C-2 in `captp_client.rs:134`). |
| Resolve a fast-path certificate | requires 2f+1 signatures | yes once cert is assembled | `fast_path.rs:430 assemble_certificate`. |
| Detect a fork / double-spend | only by re-running consensus | no | Solo mode papers over this with the assumption "single operator, no Byzantine adversary" (`solo.rs:7-12`). |

**The contract:** offline = "I can compute everything that would be valid if the world agreed with me." Consensus = "the world is forced to agree, or at least to expose disagreement." Pyana's receipt chain is the bridge: offline-built receipts become true once they've been re-executed under consensus and the resulting consensus-side chain agrees.

---

## 8. CapTP messages while offline

`captp/src/store_forward.rs:1-19`:

> When a destination node is offline, capability messages are encrypted to the destination's public key and queued on a relay (or directly in the blocklace DAG). When the destination comes online, it retrieves and decrypts pending messages, processing them in causal order.

The mechanics:

- `encrypt_for_destination` (line 165) — X25519 + ChaCha20-Poly1305 of an arbitrary plaintext.
- `MessageRelay::enqueue` (line 678) — queue at a relay node, keyed by `FederationId`.
- `MessageRelay::drain(destination)` (line 708) — destination pulls its queue.
- `MessageRelay::expire(current_height)` (line 723) — TTL-based GC.
- `queue_via_blocklace` / `scan_and_decrypt_blocklace` (lines 998, 1022) — alternate path using the blocklace DAG as the queue.

**Durability story:**
- Relay-based: lives at the relay until drained or TTL-expired. Bounded by `max_queue_depth` per destination and `max_total_messages` globally (line 666).
- Blocklace-based: lives as long as the blocklace lives — effectively the federation's durability — but message content is opaque to consensus and pays no fee (it's a `BlocklaceEnvelope::to_payload` blob).

**However**: in `sdk/src/captp_client.rs:143`, `LiveRef::send(action)` has a TODO marker:

> **Current status (audit finding C-2):** this method allocates a promise id in the local pipeline registry but does *not* yet enqueue the `action` argument for wire delivery. The argument is reserved in the signature so this becomes a no-op rename once the wire-delivery path is wired through.

`LiveRef::pipeline` (line 162) is identical (a comment confirms). **So today, the cipherclerk's CapTP path silently drops outbound messages.** The store-and-forward primitives in `captp/src/store_forward.rs` exist, but the cipherclerk's high-level send/pipeline API doesn't yet call them. The integration seam is unfinished.

**Net:** CapTP offline durability is fully spec'd and partially built. The crypto primitives exist; the relay state machine exists; the blocklace envelope format exists. What's missing is the glue from `LiveRef::send` into `StoreForwardClient::prepare_message` + `MessageRelay::enqueue` or `queue_via_blocklace`.

---

## 9. Open questions for designer

1. **Solo-mode `Tentative → Final` promotion path is not visible.** The protocol docstring in `federation/src/solo.rs:14-20` says tentative receipts are promoted to Final on rejoin. I cannot find the code that walks the cipherclerk's receipt chain, sees a `Tentative` flag, validates against the merged nullifier log, and rewrites finality. (Search: `Finality::Final` outside `executor.rs`; nothing.) Is this scheduled work, or am I missing it?

2. **`AgentRuntime` stamps `Final` on offline receipts.** `sdk/src/runtime.rs::AgentRuntime` constructs `TurnExecutor::new(...)` without setting an executor signing key or downgrading finality. Receipts produced offline therefore claim `Finality::Final` and ship with `executor_signature: None`. Is this intentional (the cclerk trusts itself unconditionally) or should `AgentRuntime` be aware that it's an unattested local executor and stamp `Finality::Tentative`?

3. **Cipherclerk receipt chain vs. consensus receipt chain divergence.** When an offline cclerk builds receipts R1..R10 and then submits the underlying turns to a node, the node's executor produces its own receipts R1'..R10' with different timestamps, federation_ids, and executor signatures. The cipherclerk's `previous_receipt_hash` populated from R10 will not match the node's `R10'.receipt_hash()` (different bytes). What's the contract for reconciling these? Should the cclerk (a) tear down its local chain on first successful node submit and rebuild from server, (b) maintain both chains and use the server's for `previous_receipt_hash`, or (c) something else? `EXECUTOR-HONESTY-AUDIT.md` and `WITNESSED-RECEIPT-CHAIN-DESIGN.md` may already answer this; the in-code answer isn't obvious from the cclerk/runtime alone.

4. **Cipherclerk-side batch submit.** Is there an intended "drain my offline turns to the federation" workflow? Today the cclerk has no such method; callers must submit one-by-one. If the cclerk has accumulated dozens of locally-applied turns, the all-or-nothing semantics of submitting them is ambiguous (what happens if turn 17 of 30 is rejected at the node?).

5. **`local_federation_id` in the offline executor.** `AgentRuntime::execute` calls `TurnExecutor::compute_signing_message(&action_unsigned, &self.executor.local_federation_id)` — but `runtime.rs:123` creates the executor with `TurnExecutor::new(...)`, which sets `local_federation_id: [0u8; 32]` (executor.rs:635). So the cclerk signs every action as if it lives in federation `0x00..00`. If that cclerk then submits to a real federation, the action signature will not validate against the node's `local_federation_id`. (The cross-federation replay defense in receipt.rs:374-378 is intentional, but it cuts both ways.) Is there an intended "set federation id on AgentRuntime" hook?

6. **CapTP wire delivery (C-2).** `LiveRef::send` and `LiveRef::pipeline` are stubs (sdk/src/captp_client.rs:143, 162). The store-forward primitives are ready. What's the intended next step? Hook `send` directly to `StoreForwardClient::prepare_message`, or route through `CapTpClient::pipeline`/`pipeline_to`? Is there a "submit to node, node enqueues" plan?

7. **Queue state divergence.** Offline-allocated queues live in the cipherclerk's local `TurnExecutor::queue_program_registry`. The node has no awareness of them until the underlying `Effect::QueueAllocate` turn is submitted. Until then, anything that depends on a queue ID derived from that allocation has no chance of validating elsewhere. Is there a doc-recommended "always allocate queues online first" workflow, or is the assumption that anyone using queues is doing so within an online runtime?

8. **Fee economics offline.** Burning 100% of fees against your own balance is fine for testing. Is it intended that long-lived offline AgentRuntimes will eventually go bankrupt to themselves? Or should the offline executor skip fee burning entirely (a "no federation, no fee distribution, refund the agent" path)?

9. **Cipherclerk receipt-chain reset on conflict.** If the cipherclerk's chain head H_offline disagrees with the node's H_online for the same agent, every subsequent cclerk-built turn is structurally invalid at the node (`ReceiptChainMismatch`). There's no public `AgentCipherclerk::reset_receipt_chain()` method. Is there an intended recovery path other than "destroy and rebuild the cclerk"?

10. **Equivocation cost.** The blocklace auto-evicts equivocators (`blocklace_sync.rs:803-823`) with `constitution.auto_evict(&proof)`. The cclerk can also auto-equivocate inadvertently by submitting two divergent chains to two different nodes (if it ever had two `TurnExecutor` instances active). Should the cclerk itself enforce that it never produces two distinct receipts at the same `(agent, nonce)`? Today it doesn't.

---

## 10. Files of interest (absolute paths)

Primary call sites:
- `/Users/ember/dev/breadstuffs/sdk/src/cipherclerk.rs` — cclerk API, sign_action/sign_turn/build_authorized_turn/prove_*/queue ops; lines 2361, 2403, 2440, 2475, 2548, 2882, 5134, 5506.
- `/Users/ember/dev/breadstuffs/sdk/src/runtime.rs` — `AgentRuntime::new` / `::execute` (offline executor wiring), lines 99, 215; hardcoded fee=10_000 at line 276.
- `/Users/ember/dev/breadstuffs/turn/src/executor.rs` — `TurnExecutor::execute`, line 2598; receipt-chain self-binding lines 594-607, 843-864; fee distribution 2816-2825; executor signing 762-776.
- `/Users/ember/dev/breadstuffs/turn/src/turn.rs` — `TurnReceipt` definition + `Finality`, lines 341-409.
- `/Users/ember/dev/breadstuffs/turn/src/verify.rs` — chain verification, lines 117, 245.
- `/Users/ember/dev/breadstuffs/turn/src/fast_path.rs` — lock table + certificate flow.
- `/Users/ember/dev/breadstuffs/turn/src/economics.rs` — `EpochMinter`, fee burn.

Federation / consensus:
- `/Users/ember/dev/breadstuffs/federation/src/solo.rs` — `FederationMode`, `NullifierLog`, rejoin protocol.
- `/Users/ember/dev/breadstuffs/federation/src/lib.rs` — top-level architecture comment + quorum math.
- `/Users/ember/dev/breadstuffs/node/src/api.rs::post_submit_turn` line 1124 — entry point that runs the cipherclerk's turn locally on the node then gossips.
- `/Users/ember/dev/breadstuffs/node/src/blocklace_sync.rs` — block dissemination, frontier sync, `execute_finalized_turn` at line 1157.

CapTP offline:
- `/Users/ember/dev/breadstuffs/captp/src/store_forward.rs` — encryption, relay queue, blocklace envelope.
- `/Users/ember/dev/breadstuffs/captp/src/session.rs` — bilateral session state.
- `/Users/ember/dev/breadstuffs/sdk/src/captp_client.rs:143` — `LiveRef::send` stub (audit finding C-2, unimplemented wire delivery).

Related design docs (not read for this audit, but the in-repo references point here):
- `/Users/ember/dev/breadstuffs/DESIGN-receipts.md`
- `/Users/ember/dev/breadstuffs/WITNESSED-RECEIPT-CHAIN-DESIGN.md`
- `/Users/ember/dev/breadstuffs/EXECUTOR-HONESTY-AUDIT.md`
- `/Users/ember/dev/breadstuffs/DESIGN-captp-integration.md`

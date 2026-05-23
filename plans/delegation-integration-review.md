# Delegation Integration Review

Analysis of how `blocklace/src/delegation.rs` (Phase 5) integrates with the existing system.

---

## 1. Does TurnExecutor Need Changes?

**Yes. Three changes needed.**

### 1a. Scope checking at execution time (REQUIRED NOW)

Currently `TurnExecutor::execute()` (`turn/src/executor.rs:1403`) validates only:
- Nonce matches agent cell
- Fee coverage from agent balance
- Budget gate (silo-level)
- Preconditions

It has no awareness that the turn's `agent` field might correspond to a client whose execution has been delegated. The executor currently assumes:
- The submitter IS the agent (their nonce, their balance, their cell)

**Change needed:** When executing a delegated turn, the executor must accept that the `agent` field is the CLIENT's cell, but the SUBMITTER is the executor. The executor needs a `delegation_context: Option<&ExecutorDelegation>` parameter (or a lookup into a DelegationManager) to:

1. Verify the executor is authorized to submit on behalf of this client
2. Check the turn is within scope
3. Deduct fees from the EXECUTOR's cell (not the client's -- the executor batches for efficiency)

**File:** `turn/src/executor.rs`
**Change:** Add `pub fn execute_delegated(&self, turn: &Turn, ledger: &mut Ledger, delegation: &ExecutorDelegation) -> TurnResult` that wraps `execute()` with scope/delegation checks. The existing `execute()` remains unchanged for direct execution.

### 1b. Batch mode (REQUIRED NOW)

`DelegationManager::collect_batch()` produces a `Vec<ClientTurnRequest>`, and the executor must:
1. Deserialize each `ClientTurnRequest.turn_data` into a `Turn`
2. Execute all turns sequentially against the ledger
3. Collect results into a `BatchExecution`
4. Produce a combined STARK proof

**File:** `turn/src/executor.rs`
**Change:** Add:
```rust
pub fn execute_batch(
    &self,
    requests: Vec<ClientTurnRequest>,
    ledger: &mut Ledger,
    delegation_mgr: &DelegationManager,
) -> Result<BatchExecution, DelegationError>
```

This method:
- Validates each request against the delegation scope
- Executes turns sequentially (order = submission order)
- Rolls back ALL if any fails (batch atomicity)
- Produces per-turn `TurnResult` structs
- Generates a batch STARK proof (initially: concatenation of individual proofs; later: aggregated)

### 1c. Batch proof generation (CAN WAIT)

True combined STARK proof over multiple turns requires circuit-level batching (Plonky3 recursive STARK or IVC accumulation). For now, the `batch_proof` field can contain the hash chain of individual turn receipts. Full proof aggregation is Phase 6.

---

## 2. Does the Wire Protocol Need New Message Types?

**Yes. Three new WireMessage variants needed.**

**File:** `wire/src/message.rs`

Currently `WireMessage` has: `PresentToken`, `PresentationResult`, `RequestAttestedRoot`, `AttestedRoot`, `SubmitRevocation`, `RevocationAck`, `RequestNonMembership`, `NonMembershipResponse`, `Hello`, `Welcome`.

None of these carry turn submission or batch results. The existing node API uses HTTP (`POST /api/submit-turn`), not wire messages. However, delegation requires executor-to-executor and client-to-executor communication over the wire protocol (not just HTTP):

### New variants:

```rust
/// Client submits a turn to their delegated executor.
DelegatedTurn {
    request: ClientTurnRequest,
},

/// Executor publishes a batch result to interested parties.
BatchResult {
    batch: BatchExecution,
},

/// Challenge message (client disputes executor behavior).
DelegationChallenge {
    challenge: Challenge,
    /// Signature proving the client issued this challenge.
    client_signature: [u8; 64],
},
```

Additionally, `Challenge` and `ChallengeReason` need `Serialize`/`Deserialize` derives (currently they only have `Clone, Debug`).

**Architectural note:** The HTTP API (`node/src/api.rs`) also needs endpoints:
- `POST /api/delegate` -- establish delegation
- `POST /api/submit-delegated` -- submit a ClientTurnRequest
- `GET /api/batch/:seq` -- fetch batch result
- `POST /api/challenge` -- issue a challenge

---

## 3. Does the SDK/Wallet Need Changes?

**Yes. The wallet needs a delegation-aware submission path.**

**File:** `sdk/src/wallet.rs`

Currently `AgentWallet` has:
- `sign_turn(&self, turn: &Turn) -> SignedTurn` (line 1742)
- No concept of "my executor" or "delegated submission"

### Changes needed:

```rust
// New fields on AgentWallet:
/// The executor this wallet has delegated to (if any).
executor_address: Option<String>,  // host:port of executor
/// The active delegation (for scope checking before submission).
active_delegation: Option<ExecutorDelegation>,

// New methods:
pub fn set_executor(&mut self, addr: String, delegation: ExecutorDelegation)
pub fn clear_executor(&mut self)
pub fn build_delegated_request(&self, turn: &Turn) -> ClientTurnRequest
pub fn verify_batch_result(&self, batch: &BatchExecution) -> Result<bool, DelegationError>
pub fn detect_censorship(&self, current_height: u64) -> bool
```

The `build_delegated_request` method:
1. Serializes the Turn to `turn_data: Vec<u8>`
2. Signs it with the wallet's signing key
3. Assigns a monotonic nonce
4. Records `submitted_at` from current known height

The `verify_batch_result` method:
1. Finds this client's TurnResult in the batch
2. Verifies the STARK proof (once aggregated proofs exist)
3. Checks `old_commitment` matches expected state
4. Checks `effects_hash` matches the turn's effects

---

## 4. Does the Node Need a "Batch Executor" Mode?

**Yes. A new `Command::Executor` subcommand is needed.**

**File:** `node/src/main.rs`

Currently the node has: `Run`, `Init`, `Status`, `Mcp`, `Genesis`, `Relay`, `Bridge`.

### New subcommand:

```rust
/// Run as a dedicated batch executor for delegated clients.
Executor {
    /// Port for the executor's HTTP/wire API.
    #[arg(long, default_value = "8422")]
    port: u16,

    /// Maximum turns per batch.
    #[arg(long, default_value = "100")]
    batch_size: usize,

    /// Maximum time to wait before producing a batch (ms).
    #[arg(long, default_value = "1000")]
    batch_timeout_ms: u64,

    /// Data directory.
    #[arg(long, default_value = "~/.pyana")]
    data_dir: String,

    /// Federation peers (executor still needs federation connectivity).
    #[arg(long, value_delimiter = ',')]
    federation_peers: Vec<String>,
}
```

The executor mode:
1. Accepts `ClientTurnRequest`s from delegated clients (HTTP + wire)
2. Batches them (up to `batch_size` or `batch_timeout`)
3. Executes the batch via `TurnExecutor::execute_batch()`
4. Publishes the `BatchExecution` as a blocklace block
5. Notifies clients of their results

**Key difference from `Run`:** The executor does NOT process its own wallet's turns as the primary path. It processes OTHER agents' turns. It still needs federation connectivity to submit batch blocks and sync state.

---

## 5. How Does Delegation Interact with CapTP?

**This is the deepest architectural question. Answer: E manages Alice's capability namespace.**

### Current model (`captp/src/session.rs`, `sdk/src/captp_client.rs`):
- Each wallet has a `CapTpClient` with its own `SwissTable` (exports) and `CapSession`s
- When Bob wants to enliven a sturdy ref to Alice's cell, he connects to Alice's node
- Alice's node holds Alice's SwissTable (maps swiss numbers to cell + permissions)

### With delegation:
- Alice delegates to Executor E
- E IS Alice's executor -- E processes Alice's turns, manages Alice's state
- Alice's `SwissTable` must live on E (because E is the authoritative holder of Alice's cell state)
- When Bob enlivens a sturdy ref to Alice's cell, he connects to E (not Alice's phone)

### Changes needed:

**File:** `sdk/src/captp_client.rs`
- `CapTpClient` needs a `delegated_swiss_tables: HashMap<[u8; 32], SwissTable>` -- one per delegated client
- When E receives an enliven request for client C's cell, it looks up C's swiss table

**File:** `captp/src/session.rs`
- `CapSession.exports` currently maps cells THIS node exports
- With delegation: E's sessions include cells belonging to delegated clients
- The `export()` method needs a `on_behalf_of: Option<[u8; 32]>` to distinguish "my export" from "delegated client's export"

**Architectural decision:** E's CapTpState includes Alice's exports. This is correct -- E is Alice's vat (in E-language terms). The sturdy ref URI should encode E's address, not Alice's:
- Current: `pyana://alice-node:9420/swiss/0xABCD`
- With delegation: `pyana://executor-e:9420/swiss/0xABCD`

Alice's swiss numbers are generated by E (or migrated from Alice's old node when delegation begins).

---

## 6. How Does Delegation Interact with the Relay?

**The relay and executor are orthogonal. Relay = storage, Executor = compute.**

### Current relay model (`node/src/relay_service.rs`):
- Relay hosts inboxes (store-and-forward for offline agents)
- Anyone can send to an inbox; the owner drains it
- Messages are CapTP `Op` messages (bootstrap, deliver, drop)

### With delegation:
- Alice's inbox remains on the relay (storage)
- E polls Alice's inbox for incoming messages (compute)
- E processes incoming CapTP ops on Alice's behalf (enlivening, deliver-to-target)

### No relay code changes needed for basic delegation.

**However:** E needs a way to authenticate as Alice's executor when draining Alice's inbox. Currently inbox drain requires knowledge of the inbox subscription credentials.

**File:** `node/src/relay_service.rs`
**Change (CAN WAIT):** Add `drain_on_behalf_of` endpoint that accepts an `ExecutorDelegation` proof. The relay verifies Alice's signature on the delegation and allows E to drain.

---

## 7. How Does Delegation Interact with Governance?

### Conflict analysis:

**Governance expects blocks from Alice's key.** In `blocklace/src/constitution.rs`, the `GovernedReferenceGroup` tracks members by their 32-byte public key. Blocks must be signed by a member key to count toward consensus.

**Delegation means E produces blocks containing Alice's turns.** But these blocks are signed by E's key, not Alice's key.

### Resolution:

This is NOT a conflict because governance operates at the blocklace level (who produces blocks?) while delegation operates at the turn level (who processes turns?).

- E produces blocks signed by E's key (E is a member of the federation/reference group)
- Those blocks contain `BatchExecution` payloads that include Alice's turns
- Alice's STRAND (in blocklace terms) still has blocks signed by Alice's key for governance votes

### Governance actions are NOT delegated:

| Operation | Who does it? | Signed by |
|-----------|-------------|-----------|
| State transition turns | E (executor) | Alice (ClientTurnRequest.client_signature) + E (block signature) |
| Governance votes | Alice (personal) | Alice |
| Constitutional proposals | Alice (personal) | Alice |
| Membership acks | Alice (personal) | Alice |

**Architectural rule:** `DelegationScope` should explicitly EXCLUDE governance operations. The `EffectsOnly` variant's `allowed_effects` byte should never include a governance-effect discriminant. The `Full` scope means "all state-transition effects" NOT "all operations including governance."

**File:** `blocklace/src/delegation.rs`
**Change (RECOMMENDED NOW):** Add a doc comment to `DelegationScope::Full` clarifying: "Full delegation covers state-transition effects only. Governance operations (votes, proposals, membership acks) are never delegable."

---

## 8. What Changes NOW vs. What Can Wait?

### PHASE 5a: Minimum viable delegation (NOW)

| Component | File | Change |
|-----------|------|--------|
| TurnExecutor | `turn/src/executor.rs` | Add `execute_delegated()` with scope check |
| TurnExecutor | `turn/src/executor.rs` | Add `execute_batch()` producing BatchExecution |
| Wire message | `wire/src/message.rs` | Add `DelegatedTurn`, `BatchResult`, `DelegationChallenge` variants |
| Wire message | `blocklace/src/delegation.rs` | Add `Serialize`/`Deserialize` to `Challenge`, `ChallengeReason` |
| Node API | `node/src/api.rs` | Add `POST /api/submit-delegated` endpoint |
| SDK | `sdk/src/wallet.rs` | Add `set_executor()`, `build_delegated_request()` |
| Node | `node/src/main.rs` | Add `Command::Executor` subcommand (minimal: accept + batch + execute) |

### PHASE 5b: Verification and censorship protection (NEXT)

| Component | File | Change |
|-----------|------|--------|
| SDK | `sdk/src/wallet.rs` | Add `verify_batch_result()`, `detect_censorship()` |
| CapTP | `sdk/src/captp_client.rs` | Delegated swiss tables |
| CapTP | `captp/src/session.rs` | Multi-owner exports |
| Relay | `node/src/relay_service.rs` | `drain_on_behalf_of` endpoint |

### PHASE 5c: Aggregated proofs and full CapTP handover (LATER)

| Component | File | Change |
|-----------|------|--------|
| Circuit | `circuit/src/` | Batch STARK aggregation (recursive proof or IVC) |
| CapTP | `captp/src/` | Swiss table migration protocol (client -> executor) |
| Governance | `blocklace/src/constitution.rs` | Explicit "non-delegable operations" enforcement |
| Reputation | NEW | Executor reputation/slashing based on challenge history |

---

## Architectural Conflicts

### Conflict 1: Nonce management

`TurnExecutor::execute()` checks `agent_cell.state.nonce == turn.nonce`. In delegated mode, who manages Alice's nonce?

- **Problem:** If Alice submits nonce 5, and E hasn't processed nonce 4 yet, nonce 5 is rejected.
- **Solution:** E is the SOLE authority on Alice's nonce (because E is the sole executor). Alice's wallet queries E for current nonce before building a ClientTurnRequest. This means Alice cannot have two executors simultaneously (already enforced by `AlreadyDelegated`).

### Conflict 2: Fee accounting

`TurnExecutor::execute()` deducts `turn.fee` from `agent_cell.state.balance`. In delegation:

- **Option A:** Client pays (fee deducted from client cell). Simple but requires client to have balance.
- **Option B:** Executor pays (batches turns, amortizes proof cost). Requires the executor to be compensated.
- **Recommendation:** Option A for now (client pays per-turn fee as today). The executor's compensation model (staking, monthly fee, etc.) is a separate economic design question.

### Conflict 3: Atomicity across batched turns

If turn 3 in a batch fails, should turns 1-2 remain committed or should the whole batch roll back?

- **Option A:** Per-turn atomicity (each turn commits or fails independently within the batch).
- **Option B:** Batch atomicity (all or nothing).
- **Recommendation:** Option A. Each `TurnResult` in the batch has its own `success` flag. The batch proof covers all turns regardless of individual success/failure. This matches Ethereum L2 sequencer semantics.

### Conflict 4: State commitment divergence

With delegated execution, Alice's canonical state is whatever E last published. If Alice goes offline and comes back, she needs to sync from E's published batches. But `verify_turn_in_batch()` only checks result presence -- it does not verify state commitments against an independently maintained local copy.

- **Resolution:** The wallet must maintain a shadow state commitment and compare against `TurnResult.new_commitment`. Any divergence triggers a challenge. This is Phase 5b.

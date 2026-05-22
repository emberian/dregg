# Owned-Cell Fast Path: LUTRIS-Style Consensusless Agreement for Pyana

Design exploration for bypassing Morpheus BFT consensus on turns that
touch only cells owned by the signer.

Status: RESEARCH / DESIGN -- not approved for implementation.

---

## 1. Motivation

Current turn processing pipeline:

```
client -> encrypt(turn) -> gossip -> Morpheus BFT ordering -> decrypt -> execute -> receipt
```

For a 4-node federation at 50ms RTT, Morpheus adds 2-3 consensus rounds
(~300-600ms) to every turn, even those that provably cannot conflict with
any other agent's turns. The Sui LUTRIS paper demonstrates that owned-object
transactions (single-writer) can skip consensus entirely, achieving finality
in 2 network round trips (~100ms at 50ms RTT).

Pyana's cell model is well-suited to this optimization: cells have a single
owner public key, turns declare their access sets upfront (in the ConflictSet
Bloom filter), and the nonce provides a natural version/sequence number.

**Expected improvement**: Latency for single-owner turns drops from ~600ms
(consensus + proof) to ~100ms (certificate collection) + 500ms (proof
generation, pipelined in parallel) = ~500ms wall-clock for proof-required
turns, ~100ms for signature-only turns. The key win is that the 500ms proof
generation runs concurrently with certificate collection, so the critical
path is max(100ms, 500ms) = 500ms vs. 600ms+500ms = 1100ms for the current
serial approach.

---

## 2. Eligibility Criteria: What Qualifies for the Fast Path

A turn qualifies for the owned-cell fast path if and only if:

1. **All cells in the write set are owned solely by the signer.**
   The `extract_access_sets()` function in `turn/src/conflict.rs` produces
   the write set. Every CellId in that set must have `cell.public_key ==
   turn.agent.public_key` at the current nonce version.

2. **Read-set cells are either owned by the signer OR are read-only
   (frozen/immutable).**
   Following Sui's precedent: reading a shared/frozen object does not
   require consensus because reads are non-mutating. However, reading
   a *mutable* cell owned by *another* agent is problematic -- the other
   agent might mutate it between our read and our execution.

3. **No shared-state effects.**
   Effects like `Transfer { from, to }` where `to` is owned by a different
   agent are fine (the transfer is authorized by the signer who owns `from`).
   But if the turn's execution depends on another agent's mutable state
   being at a specific version, it must go through consensus.

4. **No pending conditional dependencies.**
   If `turn.depends_on` is non-empty, the turn cannot use the fast path
   (it requires coordination with the PendingTurnRegistry).

### 2.1 Capability Delegation Chains

**Open question for ember**: If Alice's cell has a `CapabilityRef` pointing
to Bob's cell, and Alice's turn reads Bob's cell via that capability:

- Option A: This disqualifies from fast path (conservative). Alice is reading
  Bob's mutable state, which could change between certificate collection and
  execution.
- Option B: Allow if the capability is exercised read-only AND Bob's cell is
  frozen/has no active writers at the current version.
- Option C: Allow unconditionally if the turn only uses the capability for
  authorization checking (doesn't read Bob's state fields).

**Recommendation**: Start with Option A (conservative). Refine later once
the happy path is proven.

### 2.2 `ExerciseViaCapability` Effects

These present a subtlety: the inner effects modify cells that may not be
owned by the signer. For example, Alice exercises a capability on Bob's cell
to modify Bob's state. This is NOT eligible for the fast path because:

- Bob could simultaneously submit a turn modifying his own cell
- Without consensus, these two turns could conflict

The fast path must reject any turn containing `ExerciseViaCapability` effects
unless the target cell is also owned by the signer (self-capability exercise).

---

## 3. The Locking Protocol

### 3.1 Nonce-as-Lock

Sui uses per-object version locks (OwnedLock[ObjKey] -> TxSign). In pyana,
cells already have a monotonically increasing nonce in `CellState`. The
natural analog:

```
CellLock[(CellId, nonce)] -> Option<TurnSign>
```

When a validator receives a fast-path turn:
1. Check `turn.nonce == cell.state.nonce` (current version)
2. Check `CellLock[(cell.id, nonce)] == None` (no competing lock)
3. Atomically set `CellLock[(cell.id, nonce)] = sign(turn)`
4. Return signature to client

This prevents equivocation: if the agent tries to submit two different turns
with the same nonce, at most one can collect 2f+1 signatures.

### 3.2 Multi-Cell Locking

A turn that writes multiple cells (all owned by the signer) must lock ALL of
them atomically at the validator. If any lock fails, all acquired locks for
this turn must be released.

This is analogous to Sui Algorithm 1, Check 1.3-1.4: acquire mutex over all
inputs, then set OwnedLock for each.

### 3.3 Interaction with Consensus Path

**Critical safety property**: A fast-path turn and a consensus-path turn
must never both execute on the same cell at the same nonce.

Protocol:
- If a turn is on the fast path, validators lock the cell nonce immediately.
- If a turn is routed through consensus (because it touches shared cells),
  validators still lock the owned cells when processing the transaction
  (before forwarding to consensus). This is exactly what Sui does.
- Consensus-sequenced turns that find a cell already locked by a different
  turn must wait for the lock to resolve (either the fast-path turn
  completes and bumps the nonce, or the lock expires).

### 3.4 Lock Expiry

**Open question for ember**: How long should a cell stay locked for a pending
fast-path turn?

Options:
- **Per-epoch expiry** (Sui's approach): Locks expire at epoch boundary.
  Client equivocation only costs liveness for the remainder of the epoch.
- **Timeout-based**: Lock expires after N blocks (e.g., 100 blocks).
  Shorter recovery from client crashes.
- **Fast unlock via quorum** (Stingray-style): If 2f+1 validators agree
  the lock should be released (e.g., client provably offline), release early.

**Recommendation**: Timeout-based with fast unlock. The BudgetGate already
has a `fast_unlock` mechanism -- reuse the same pattern. Default timeout:
50 blocks (~50 seconds at 1s block time).

---

## 4. Certificate Structure

### 4.1 What Validators Sign

In Sui, validators sign the transaction itself (the TxSign). In pyana:

**Option A: Sign the turn hash.**
```rust
struct TurnSign {
    turn_hash: [u8; 32],
    agent: CellId,
    nonce: u64,
    validator_id: NodeId,
    signature: Ed25519Signature,
}
```
Minimal, fast. But the validator hasn't verified the turn's effects are valid.

**Option B: Sign the turn hash + conflict set commitment.**
```rust
struct TurnSign {
    turn_hash: [u8; 32],
    conflict_set_commitment: [u8; 32],
    agent: CellId,
    nonce: u64,
    validator_id: NodeId,
    signature: Ed25519Signature,
}
```
Binds the signature to the declared access set, preventing conflict-set
swapping after certificate formation.

**Option C: Sign turn hash + validity proof hash.**
This would bind the signature to the proof, but requires the proof to be
available at signature-collection time (see Section 5).

**Recommendation**: Option B. The conflict set commitment is already in the
`TurnValidityPublicInputs` struct, so no new data needs to be transmitted.
This provides:
- Anti-equivocation (nonce binding)
- Access set binding (conflict set commitment)
- Agent binding (CellId)

### 4.2 Certificate Formation

```rust
struct TurnCertificate {
    turn_hash: [u8; 32],
    conflict_set_commitment: [u8; 32],
    agent: CellId,
    nonce: u64,
    signatures: Vec<(NodeId, Ed25519Signature)>, // >= 2f+1
}
```

The client (or a gateway) collects 2f+1 `TurnSign` responses and assembles
the certificate. The certificate is then sent back to validators for
execution.

### 4.3 Effects Certificate (Settlement)

After execution, validators sign the receipt (effects). The client can
collect 2f+1 effects signatures to form an effects certificate, providing
settlement finality. This is the `TurnReceipt` + executor signatures.

---

## 5. Interaction with ZK Proofs

### 5.1 The Pipelining Question

Current flow for encrypted turns:
```
1. Client generates STARK proof (500-800ms)
2. Client encrypts turn + attaches proof
3. Federation orders, decrypts, verifies proof, executes
```

Proposed fast-path flow:
```
1. Client signs turn (plaintext -- no encryption needed on fast path!)
2. Client broadcasts to validators for locking + signature collection (~100ms)
3. IN PARALLEL: Client generates STARK proof (500-800ms)
4. Client assembles certificate (from step 2 signatures)
5. Client sends certificate + proof to validators for execution
```

**Key insight**: On the fast path, the turn content does NOT need to be
encrypted because the access set only contains the signer's own cells. There
is no privacy concern -- the signer is revealing their own state transitions.

**However**: If the turn has committed-field state (FieldVisibility::Committed
or SelectivelyDisclosable), the proof is still needed to validate the state
transition without revealing the hidden values.

### 5.2 Must the Proof Be Part of What Validators Sign?

**No.** Validators sign the turn hash (which commits to the turn content).
The proof is verified at execution time, not at lock time. This enables the
pipeline:

- Lock phase: validators verify signature, nonce, fee sufficiency (cheap checks)
- Execution phase: validators verify STARK proof, execute effects

This is safe because:
- If the proof is invalid, execution fails, but the lock is consumed (nonce
  bumped). The agent loses the fee but cannot equivocate.
- The certificate guarantees the turn will eventually execute (or timeout).
  It does NOT guarantee success -- same as Sui.

### 5.3 When Proofs Are Not Required

Many fast-path turns won't need STARK proofs at all:
- Simple transfers between the agent's own cells (signature auth only)
- Nonce bumps
- State field updates on public-visibility cells

For these, the fast path achieves ~100ms finality (2 RTTs) with no proof
generation at all. This is the true win.

### 5.4 When Proofs ARE Required

Turns that modify committed/selectively-disclosable state fields need proofs.
The proof proves the state transition is valid without revealing hidden values.
In this case:
- Proof generation runs in parallel with certificate collection
- Certificate collection: ~100ms (2 RTTs)
- Proof generation: 500-800ms
- Execution starts at: max(100ms, 500ms) = 500ms
- Total: ~550ms (vs. ~1100ms today for consensus + serial proof)

---

## 6. Interaction with Existing Subsystems

### 6.1 PendingTurnRegistry

Turns with `depends_on` or conditional resolution cannot use the fast path.
They require coordination that only consensus ordering can provide.

Fast-path turns that produce receipts DO satisfy `ResolutionCondition::
AwaitReceipt` conditions in the PendingTurnRegistry. A fast-path receipt
is just as valid as a consensus-path receipt.

### 6.2 BudgetGate (Stingray Bounded Counters)

The BudgetGate check happens BEFORE execution (after fee/nonce commitment).
On the fast path:

- Lock phase: validator checks `BudgetSlice.remaining() >= turn.fee`
- If insufficient: reject (don't sign)
- If sufficient: tentatively debit, then sign

The tentative debit is rolled back if the turn never executes (lock expires
without certificate). This uses the existing `BudgetGate::fast_unlock()`.

**Subtle issue**: The budget check at lock time uses the slice state at that
moment. By the time the certificate arrives for execution, the slice might
have been further debited by other turns. Solution: the lock-time debit is
the reservation. Execution honors the reservation.

### 6.3 Revocation Checking

The `RevocationFilter` (cuckoo filter in `token/src/revocation.rs`) is
checked at execution time, not lock time. A capability might be revoked
between lock and execution.

This is acceptable: revocation affects authorization, not ordering. If a
capability is revoked after locking but before execution, the turn fails
at execution time (fee still charged, nonce bumped). This matches Sui's
behavior -- a transaction can fail even after certificate formation.

### 6.4 Encrypted Turns

Fast-path turns do NOT need encryption (they only touch the signer's cells,
no privacy from other agents is needed). The `EncryptedTurn` wrapper is
unnecessary.

However, there is a nuance: if the signer wants privacy from the *validators*
(e.g., hiding state field values that are committed), the turn body could
still be encrypted to a threshold key. But this adds latency (threshold
decryption). Initial design: fast-path turns are plaintext.

### 6.5 ConflictSet (Bloom Filter)

On the fast path, the conflict set is still computed and included in the
certificate (as the `conflict_set_commitment`). Validators use it to:
- Verify the turn is truly single-owner (no bits overlap with other agents' cells)
- Detect if a consensus-path turn might conflict with a pending fast-path lock

The ConflictSet becomes a coordination mechanism between the two paths.

---

## 7. Fallback to Consensus

### 7.1 When Fast-Path Is Rejected

A turn is re-routed to consensus when:

1. **Lock conflict**: Another turn already holds the lock for this cell+nonce.
   The agent equivocated or there's a race condition.
2. **Insufficient signatures**: Client cannot collect 2f+1 within timeout.
   Validators might be down or network partitioned.
3. **Eligibility check fails**: Turn touches cells not owned by the signer
   (detected at lock time by validators).
4. **Budget exhausted**: The silo's BudgetSlice cannot cover the fee.

### 7.2 Timeout Handling

If the client broadcasts a turn but fails to form a certificate:
- Locks expire after the configured timeout (50 blocks / ~50 seconds)
- The agent can retry with the same nonce (locks were released)
- OR the agent can submit a new turn with the same nonce via consensus

**Equivocation recovery**: If an agent submits conflicting turns (different
content, same nonce), at most one can succeed. The locked cells prevent
double-spend. After epoch boundary, all stale locks are cleared and the
agent regains liveness (matching Sui's per-epoch equivocation forgiveness).

### 7.3 Lock Expiry and State Divergence

When a lock expires without execution:
- `CellLock[(cell.id, nonce)] = None` (reset)
- `BudgetGate::fast_unlock()` refunds the tentative debit
- The cell state is unchanged (no nonce bump, no balance change)
- The agent is free to submit a new turn for this cell

---

## 8. Performance Analysis

### 8.1 Latency Comparison

| Scenario | Current (Consensus) | Fast Path |
|----------|-------------------|-----------|
| Signature-only turn (no proof) | 600ms (3 consensus rounds) | 100ms (2 RTTs) |
| Proof-required turn | 600ms + 500ms = 1100ms (serial) | 500ms (proof || cert) |
| Shared-cell turn | 600ms | 600ms (no change) |
| Conditional turn | 600ms + wait | 600ms + wait (no change) |

### 8.2 Throughput Impact

- Fast-path turns bypass Morpheus entirely -> zero consensus load for them
- Morpheus capacity freed up for shared-cell and conditional turns
- Per-cell locking is O(1) per validator (hash table lookup)
- Certificate verification is O(n) where n = committee size (signature checks)

### 8.3 Bandwidth

- Each fast-path turn requires broadcasting to all validators (same as today)
- Additionally requires collecting signatures (new: n responses back)
- Certificate re-broadcast to all validators (new, but small: ~2KB with
  aggregated signatures)
- Net: ~2x bandwidth for fast-path turns vs. current encrypted submission.
  Acceptable given the 6x latency improvement.

### 8.4 Storage

Per-validator new storage:
- `CellLock` table: O(active_turns) entries, each ~96 bytes
- Expected: small (most turns finalize quickly, locks are transient)

---

## 9. What Sui Gets Wrong / Doesn't Apply

### 9.1 Read/Write Set Discovery

Sui's Move VM determines read/write sets during execution -- the validator
must actually run the transaction to know what it touches. This means
validators do speculative execution.

Pyana declares read/write sets upfront in the turn structure (via
`extract_access_sets()` and the ConflictSet). This is BETTER for the fast
path because:
- Eligibility can be determined before execution
- No speculative execution needed at lock time
- The conflict set commitment in the certificate is binding

### 9.2 Privacy

Sui has no privacy layer. In pyana, the encrypted turn system provides
privacy for shared-cell turns (hiding content until after ordering). The
fast path operates in a different regime: single-owner turns where privacy
from other agents is not a concern. The two mechanisms are complementary,
not conflicting.

### 9.3 Shared Object Performance

Sui's shared-object path is slow (full consensus). In pyana, we could
potentially do better for certain shared-cell patterns:

- **Read-only shared cells** (frozen configuration): Same as Sui, reads
  don't require consensus.
- **Commutative operations** (e.g., counter increments, set insertions):
  Could use CRDT-style conflict-free execution without consensus. This is
  a separate optimization beyond the scope of this design.
- **Multi-party atomic swaps**: Still require consensus (or a separate
  2PC protocol via the coordinator in `coord/src/atomic.rs`).

### 9.4 Equivocation Forgiveness

Sui forgives equivocation at epoch boundaries (locks reset). Pyana could
do better with timeout-based lock expiry + fast unlock quorum. An
equivocating agent loses at most `timeout_blocks` of liveness, not an
entire epoch.

---

## 10. Risks and Tradeoffs

### 10.1 Complexity

**Risk**: Adding a second execution path (fast + consensus) creates protocol
complexity and potential for safety bugs at the boundary.

**Mitigation**: The two paths share the same execution engine (TurnExecutor).
The difference is only in ordering/authorization. The CellLock table is the
single point of coordination.

### 10.2 Client Complexity

**Risk**: Clients must implement certificate collection logic (broadcast to
all validators, wait for 2f+1 responses, assemble certificate, re-broadcast).

**Mitigation**: This can be handled by a gateway/relay. The agent signs the
turn; a gateway handles the mechanical broadcast/collect/assemble.

### 10.3 Lock Starvation

**Risk**: A malicious agent could lock cells and never form a certificate,
blocking those cells for the timeout period.

**Mitigation**: Lock timeout (50 blocks). Plus, the agent can only lock
cells they own -- they're only hurting themselves. A self-DoS is not a
protocol concern.

### 10.4 Partition Behavior

**Risk**: During a network partition, a client might collect signatures from
a subset of validators that doesn't constitute a quorum, while the other
partition has its own locks.

**Mitigation**: The 2f+1 threshold guarantees that any two quorums overlap
by at least one honest validator. The same safety argument as Sui applies.

### 10.5 Proof Timing

**Risk**: If proof generation takes longer than expected (>800ms), the
pipeline benefit diminishes. The proof must be available before execution.

**Mitigation**: The certificate provides finality guarantee even without the
proof. Execution (settlement) waits for the proof, but the agent knows the
turn WILL execute once the proof is submitted. No other turn can conflict.

---

## 11. Open Questions for Ember

1. **Capability delegation scope**: Should turns exercising capabilities on
   other agents' cells ever be eligible? (Section 2.1, recommend: no)

2. **Lock timeout value**: 50 blocks? 100 blocks? Epoch-based? What's the
   expected block time for the federation? (Section 3.4)

3. **Plaintext vs. encrypted**: Are we comfortable with fast-path turns being
   plaintext (visible to validators)? Is there a use case for single-owner
   turns that still need validator-privacy? (Section 6.4)

4. **Signature aggregation**: Should we use BLS aggregate signatures for the
   certificate (smaller cert, but adds BLS dependency) or stick with Ed25519
   multi-sig (larger cert, existing dependency)? The morpheus crate already
   has BLS machinery.

5. **Gateway architecture**: Who collects signatures? The client directly
   (P2P library needed in client SDK) or a designated gateway node?

6. **Epoch-boundary semantics**: When a reconfiguration happens mid-flight
   (cell locked, certificate not yet formed), what happens? Sui has a
   complex reconfiguration protocol for this. Do we need one?

7. **Fast-path-only federation mode**: Some small federations might want to
   run entirely on the fast path (no consensus at all). Is this a use case
   to design for now, or future work?

8. **Budget interaction detail**: When a lock expires and budget is refunded,
   should the refund be immediate (local slice credit) or require coordinator
   acknowledgment?

---

## 12. Recommendation

**Pursue this, but phase it.**

The fast path provides a material latency improvement (6x for non-proof
turns, 2x for proof-required turns) with manageable complexity. The pyana
architecture is well-positioned for it because:

- Cells have single owners (natural LUTRIS ownership model)
- Access sets are declared upfront (no speculative execution)
- Nonces provide natural version numbers (lock key)
- The BudgetGate already has fast-unlock patterns
- The ConflictSet Bloom filter enables cross-path coordination

### Phased Implementation

**Phase 1** (2-3 weeks): Core locking protocol
- `CellLock` table in store crate
- `TurnSign` / `TurnCertificate` types
- Eligibility check (`is_fast_path_eligible(turn, ledger) -> bool`)
- Lock acquisition/release at validators
- Lock timeout with expiry checking

**Phase 2** (2-3 weeks): Client-side certificate collection
- Broadcast turn to all federation peers via gossip
- Collect signatures, form certificate
- Re-broadcast certificate for execution
- New gossip topic: `pyana/fast-path-signs`

**Phase 3** (1-2 weeks): Proof pipelining
- Parallel proof generation during certificate collection
- Certificate + proof submission for execution
- Deferred execution (wait for proof arrival after cert)

**Phase 4** (1-2 weeks): Integration and testing
- Wire into node's turn submission API
- Interaction testing with PendingTurnRegistry
- Interaction testing with BudgetGate
- Equivocation / partition property tests

**Total estimate**: 6-10 weeks of focused work, assuming the morpheus adapter
and gossip layer are stable.

---

## 13. References

- Sui LUTRIS paper: `/Users/ember/hellas/proto-dumping-ground/sui-paper.txt`
- Mini-Sui validator prototype: `/Users/ember/hellas/mini-sui/src/validator.rs`
- BCB algorithms: `/Users/ember/hellas/proto-dumping-ground/mini-sui/src/validator.rs`
- Pyana turn structure: `/Users/ember/dev/breadstuffs/turn/src/turn.rs`
- Conflict detection: `/Users/ember/dev/breadstuffs/turn/src/conflict.rs`
- Cell model: `/Users/ember/dev/breadstuffs/cell/src/cell.rs`
- Budget gate: `/Users/ember/dev/breadstuffs/turn/src/budget_gate.rs`
- Pending registry: `/Users/ember/dev/breadstuffs/turn/src/pending.rs`
- Morpheus consensus: `/Users/ember/dev/breadstuffs/federation/src/consensus.rs`
- Encrypted turns: `/Users/ember/dev/breadstuffs/turn/src/encrypted.rs`
- Federation gossip: `/Users/ember/dev/breadstuffs/node/src/federation_sync.rs`
- Stingray bounded counters: `/Users/ember/dev/breadstuffs/coord/src/budget.rs`

---

## 14. Proposed Answers to Open Questions

### Q1: Does ExerciseViaCapability on another agent's cell disqualify from fast path?

**Answer: Yes, always disqualified unless the capability target is also owned by the signer.**

**Justification from codebase**: In `turn/src/conflict.rs` lines 245-255, `extract_access_sets` already tracks inner effects of `ExerciseViaCapability` into the write set. If any inner effect targets a cell not owned by the signer (which is the typical case -- that is the whole point of `ExerciseViaCapability`), that cell appears in the write set. The eligibility check (`is_fast_path_eligible`) inspects the write set and rejects if any cell's `public_key != turn.agent.public_key`.

In `turn/src/executor.rs` lines 1966-2084, `ExerciseViaCapability` looks up a slot in the actor's c-list and applies inner effects against `cap_target` -- which is a cell belonging to another agent. This means both agents might simultaneously modify that cell (Bob via his own turn, Alice via her capability), creating a classic write-write conflict that only consensus can resolve.

**What Sui does**: Sui has no direct analogy to capability exercise, but shared objects (mutable objects accessible by multiple addresses) always require consensus. A capability that points to another agent's cell makes it a "shared-like" access pattern.

**What minimizes complexity**: The existing `extract_access_sets` function already captures ExerciseViaCapability targets in the write set, so the eligibility check falls out naturally from the existing conflict detection infrastructure. No special-casing needed.

Self-capability exercise (where cap_target is owned by the signer) is fine -- it is just an indirect way to modify one's own cell.

---

### Q2: Lock timeout duration?

**Answer: 30 blocks (~30 seconds at 1-second block time), with fast-unlock quorum as escape hatch.**

**Justification from codebase**: The BudgetGate in `turn/src/budget_gate.rs` already has a `fast_unlock` pattern (line 145) where debits are refunded on failure. The Stingray `FastUnlockManager` in `coord/src/budget.rs` (lines 514-686) provides a full 2f+1 quorum-based unlock protocol with `UnlockRequest` / `UnlockVote` / `UnlockCertificate`. This exact same machinery can be reused for cell lock release.

**What Sui does**: Per-epoch expiry. Sui's epochs are 24 hours in production (paper Section 1, line 94: "current epoch length is 24h"). This is too long for pyana -- we want sub-minute recovery from client crashes.

**Why 30 blocks, not 50**: The design doc originally proposed 50 blocks. However:
- An equivocating/crashed client only self-DoSes (they own the locked cells)
- 30 blocks provides fast liveness recovery (30s at 1s/block)
- The fast-unlock quorum (reusing `coord/src/budget.rs`'s `FastUnlockManager` pattern) provides an even faster escape if 2f+1 validators agree the client is offline
- Pyana's epoch length is 10000 blocks (`federation/src/epoch.rs` line 22: `DEFAULT_EPOCH_LENGTH: u64 = 10000`), so 30 blocks is 0.3% of an epoch -- negligible liveness cost

If the fast-unlock quorum succeeds before the 30-block timeout, the lock is released immediately. The timeout is just the fallback.

---

### Q3: Can fast-path turns carry ZK proofs, or only the proof-free subset?

**Answer: Both. Fast-path turns can carry proofs, but proofs are pipelined (verified at execution time, not at lock time).**

**Justification from codebase**: The executor in `turn/src/executor.rs` separates authorization verification (lines 1078-1156) from the budget gate check (lines 396-420). The ZK proof verification (`verify_zk_proof`, lines 1326-1380) happens during `execute_tree` in Phase 2, which is after the nonce/fee commitment in Phase 1.

For the fast path, validators sign (lock) after checking only:
- Signature validity (agent owns the cells)
- Nonce freshness
- Fee sufficiency (balance check + budget gate)

The ZK proof is verified AFTER the certificate is formed, at execution time. This is safe because:
1. If the proof is invalid, execution fails, fee is charged, nonce bumps. No state corruption.
2. The certificate guarantees the turn will be attempted (prevents equivocation), not that it will succeed.
3. This is exactly what Sui does -- transaction validity != execution success.

Proof generation (500-800ms) runs in parallel with certificate collection (100ms). The certificate arrives first; execution waits for the proof attachment. Total latency: ~500ms for proof-required fast-path turns vs. ~1100ms in the current serial pipeline.

**Proof-free turns** (simple transfers, nonce bumps, public-field updates) achieve the full 100ms latency -- these are the primary target for Phase 1.

---

### Q4: Plaintext vs. encrypted policy for fast-path turns?

**Answer: Plaintext by default. Encrypted fast-path turns are a future extension only if validator-privacy is needed for committed fields.**

**Justification from codebase**: The design doc Section 6.4 already identifies the key insight: fast-path turns only touch the signer's own cells, so there is no inter-agent privacy concern. The `EncryptedTurn` wrapper (in `turn/src/encrypted.rs`) exists to hide turn content from validators during ordering -- but on the fast path, there is no ordering step to hide from.

The one exception is `FieldVisibility::Committed` or `SelectivelyDisclosable` state fields. These hide values from validators even for the cell owner. However:
- If the field values are hidden, the ZK proof proves the state transition is valid
- The proof does not reveal the hidden values
- The turn structure (which cells, which fields) is visible, but the VALUES are opaque
- This is already sufficient privacy for the committed-field use case

Adding threshold decryption to the fast path would add 1-2 RTTs of latency (defeating the purpose) and require validators to cooperate synchronously. Initial design: fast-path turns are plaintext. If a use case requires validator-privacy for owned cells, that turn can simply use the consensus path.

---

### Q5: Epoch boundary behavior (locks spanning epoch transitions)?

**Answer: Locks do NOT survive epoch boundaries. All pending locks are force-expired at the epoch transition. Clients must re-submit.**

**Justification from codebase**: In `federation/src/epoch.rs`, `apply_epoch_transition` (lines 263-308) updates the epoch config, advances the epoch number, and applies membership changes. The reconfiguration in `mini-sui/src/reconfiguration.rs` shows the Sui pattern: `pause_tx_locking()` is called during the EndOfEpoch phase (line 126), stopping new locks from being created.

**What Sui does**: Locks expire at epoch boundary. The paper (Section 1, lines 88-95) states: "client bugs only affect the liveness of a single epoch." The equivocation forgiveness mechanism relies on this -- a client that equivocated and deadlocked their objects regains access when the epoch changes. This is the same for pyana.

**Concrete protocol at epoch boundary**:
1. At `epoch_start_height + epoch_length - LOCK_GRACE_PERIOD` (e.g., last 100 blocks): stop accepting NEW fast-path lock requests. New turns must go through consensus.
2. At epoch boundary: clear all entries in the `CellLock` table. Any pending fast-path turns that did not form a certificate in time are abandoned.
3. After epoch boundary: the new validator set begins accepting locks again.

The `LOCK_GRACE_PERIOD` prevents locks from being created so close to the boundary that they could never complete. With 30-block lock timeout and a 100-block grace period, there is a 70-block window for completion.

Any in-flight turn that had a valid certificate formed (2f+1 signatures) but was not yet executed is still valid in the new epoch -- the certificate itself is proof of authorization. Validators in the new epoch execute it upon presentation. This matches Sui's certificate persistence across epochs.

---

### Q6: Interaction with BudgetGate?

**Answer: The budget gate check happens at lock time (Phase 0.5). A tentative debit is created when the validator signs the lock. On lock expiry or execution failure, `fast_unlock` refunds immediately. On successful execution, the debit is finalized.**

**Justification from codebase**: The existing flow in `turn/src/executor.rs` lines 396-420 is:
1. `gate.try_debit(turn.fee, &turn_hash)` -- tentatively debit
2. On forest failure: `gate.fast_unlock(*fee, digest)` -- refund

For the fast path, the same pattern applies at the validator's lock-time processing:
```
Lock time:  BudgetGate.try_debit(fee, turn_hash) -> Ok(digest) -> sign lock
Expiry:     BudgetGate.fast_unlock(fee, &digest) -> refund slice
Execution:  (debit already committed; no additional action needed)
```

The `BudgetSlice` in `turn/src/budget_gate.rs` (lines 23-92) tracks debits by digest and supports refund via `refund(amount, digest)`. The validator stores the debit digest alongside the lock entry, so it can refund precisely on lock expiry.

**Subtle correctness point**: The design doc Section 6.2 identifies that the budget check at lock time uses the slice state at that moment. If other turns debit from the same slice between lock time and execution time, the slice might not have enough. Solution: the lock-time debit IS the reservation. The budget is committed at lock time, not at execution time. If the lock expires without execution, the refund restores it. This matches how `try_debit` works -- once debited, the amount is reserved regardless of what happens next.

The `BudgetGate` does NOT need version-checking for fast-path turns because the lock timeout (30 blocks) is vastly shorter than the budget rebalancing period. However, if an epoch boundary occurs (clearing locks), the BudgetGate's `expected_version` should also be bumped to reject stale locks -- this already happens via `set_expected_version()` in the gate.

---

### Q7: Should validators execute locally before signing, or just validate inputs?

**Answer: Validators do NOT execute at lock time. They validate only: signature, nonce, fee, ownership, and access set correctness. Execution happens AFTER the certificate is formed.**

**Justification from codebase**: Pyana declares access sets upfront in the turn structure (via `extract_access_sets()` in `turn/src/conflict.rs`). This is the key advantage over Sui, which must speculatively execute to discover access sets.

At lock time, validators perform the following cheap checks:
1. **Signature**: agent's Ed25519 signature is valid over the turn hash (same as `verify_ed25519_signature` in executor.rs lines 1260-1319)
2. **Nonce**: `turn.nonce == cell.state.nonce` (same check as executor.rs line 373)
3. **Fee**: `cell.state.balance >= turn.fee` (same check as executor.rs line 385)
4. **Ownership**: all cells in write set have `public_key == turn.agent.public_key`
5. **Lock availability**: `CellLock[(cell_id, nonce)] == None` for all write-set cells
6. **Budget**: `BudgetGate.try_debit(fee) -> Ok`

These are all O(1) hash-table lookups or signature verifications. No precondition evaluation, no effect application, no proof verification. The turn is NOT executed.

**What Sui does**: Algorithm 1 in the paper performs `valid(Tx, [Obj])` which checks authorization and gas sufficiency, but does NOT execute (no `exec(Tx, ...)` call at this stage). Execution happens in Algorithm 4 (process certificate). Pyana follows the same split.

**Why not execute at lock time**: Execution has side effects (balance changes, field mutations). If the turn fails to form a certificate (insufficient signatures), those side effects must be rolled back. Running execution on potentially-abandoned turns wastes compute and complicates the journal. Keep lock-time checking cheap and stateless (relative to the effects layer).

---

### Q8: Conflict resolution: fast-path vs. consensus-path turns?

**Answer: The CellLock table is the single source of truth. Consensus-path turns that touch owned cells ALSO acquire locks before they enter consensus. If a lock is held by a fast-path turn, the consensus-path turn must wait for it to resolve (complete or expire).**

**Justification from codebase**: In `mini-sui/src/validator.rs` lines 249-287 (`process_tx_internal`), Sui locks ALL owned inputs for EVERY transaction -- whether it will go through the fast path (owned-only) or consensus (shared+owned). The lock is acquired in the same codepath regardless of path routing. This is essential: without it, a consensus-path turn could modify a cell that a fast-path turn has already locked.

In pyana, the same principle applies. When a turn arrives at a validator:
1. Route determination: Is it fast-path eligible? (all write-set cells owned by signer, no depends_on, no shared reads)
2. **Regardless of routing**: acquire `CellLock[(cell_id, nonce)]` for every cell in the write set
3. If fast-path: return TurnSign immediately
4. If consensus-path: forward to Morpheus after locking

This means:
- Two fast-path turns on the same cell + nonce: at most one collects 2f+1 signatures (BFT quorum intersection prevents equivocation)
- A fast-path turn and a consensus-path turn on the same cell + nonce: at most one acquires the lock. The loser either waits (consensus path has ordering patience) or fails (fast path client gets a lock-conflict error)
- Two consensus-path turns: ordered by Morpheus consensus; locks ensure owned inputs are not double-spent between ordering and execution

**Conflict semantics**:
- Lock-conflict at a validator: validator returns an error to the fast-path client (similar to `SuiError::ObjectLocked` in `mini-sui/src/storage.rs` line 155). The client knows their turn MAY conflict and can retry or fallback to consensus.
- If the fast-path turn's lock expires (no certificate formed), the consensus-path turn can proceed.
- If the fast-path turn completes (certificate formed + executed), the consensus-path turn finds a new nonce and must be rejected as stale.

The ConflictSet Bloom filter (from `turn/src/conflict.rs`) provides an additional optimization: if a consensus-path turn's conflict set does NOT overlap with any pending fast-path locks, it can skip waiting entirely. This is a fast-out check before the per-cell lock lookup.

---

## 15. Implementation Sketch

### New Types (in `turn/src/fast_path.rs`)

```rust
/// Lock entry in the per-validator CellLock table.
/// Key: (CellId, nonce) -- identifies a specific cell at a specific version.
pub struct CellLockEntry {
    /// The turn that holds this lock.
    pub turn_hash: [u8; 32],
    /// The agent that submitted the turn.
    pub agent: CellId,
    /// Block height at which the lock was acquired.
    pub locked_at_height: u64,
    /// Budget debit digest (for refund on expiry).
    pub budget_digest: Option<DebitDigest>,
}

/// Validator's signature on a fast-path turn (partial certificate).
pub struct TurnSign {
    pub turn_hash: [u8; 32],
    pub conflict_set_commitment: [u8; 32],
    pub agent: CellId,
    pub nonce: u64,
    pub validator_id: NodeId,
    pub signature: Ed25519Signature,
}

/// A complete fast-path certificate (2f+1 TurnSigns).
pub struct TurnCertificate {
    pub turn_hash: [u8; 32],
    pub conflict_set_commitment: [u8; 32],
    pub agent: CellId,
    pub nonce: u64,
    pub signatures: Vec<(NodeId, Ed25519Signature)>,
}

/// Configuration for the fast-path locking subsystem.
pub struct FastPathConfig {
    /// Lock timeout in blocks (default: 30).
    pub lock_timeout_blocks: u64,
    /// How many blocks before epoch end to stop accepting new locks.
    pub epoch_grace_period: u64,
}

impl Default for FastPathConfig {
    fn default() -> Self {
        Self {
            lock_timeout_blocks: 30,
            epoch_grace_period: 100,
        }
    }
}
```

### New Functions

```rust
/// Determine if a turn is eligible for the fast path.
///
/// Checks:
/// 1. depends_on is empty
/// 2. All cells in write set are owned by turn.agent
/// 3. All cells in read set are either owned by turn.agent or frozen/immutable
/// 4. No ExerciseViaCapability targeting non-owned cells
pub fn is_fast_path_eligible(turn: &Turn, ledger: &Ledger) -> bool;

/// Validator lock-time processing. Returns a TurnSign on success.
///
/// Performs cheap checks (sig, nonce, fee, ownership, lock availability, budget)
/// without executing the turn. Atomically acquires locks for all write-set cells.
pub fn process_fast_path_lock(
    turn: &Turn,
    validator_id: NodeId,
    signing_key: &SigningKey,
    lock_table: &mut CellLockTable,
    ledger: &Ledger,
    budget_gate: &mut BudgetGate,
    config: &FastPathConfig,
    current_height: u64,
) -> Result<TurnSign, FastPathError>;

/// Assemble a certificate from collected TurnSigns.
/// Verifies quorum (>= 2f+1) and signature validity.
pub fn assemble_certificate(
    turn_hash: [u8; 32],
    signs: Vec<TurnSign>,
    threshold: usize,
    validator_keys: &[(NodeId, VerifyingKey)],
) -> Result<TurnCertificate, FastPathError>;

/// Execute a certified fast-path turn.
///
/// Verifies the certificate, then delegates to TurnExecutor::execute().
/// On success, bumps nonce and clears locks. On failure, clears locks and
/// refunds budget.
pub fn execute_certified_turn(
    cert: &TurnCertificate,
    turn: &Turn,
    executor: &TurnExecutor,
    ledger: &mut Ledger,
    lock_table: &mut CellLockTable,
) -> TurnResult;

/// Expire stale locks at the current block height.
/// Called once per block by the validator's block processing loop.
pub fn expire_stale_locks(
    lock_table: &mut CellLockTable,
    budget_gate: &mut BudgetGate,
    current_height: u64,
    timeout: u64,
);

/// Clear all locks (called at epoch boundary).
pub fn clear_all_locks(
    lock_table: &mut CellLockTable,
    budget_gate: &mut BudgetGate,
);
```

### New Storage (in `store/src/tables.rs`)

```rust
/// The CellLock table: maps (CellId, nonce) -> Option<CellLockEntry>
///
/// Uses the same store backend as the rest of the validator state.
/// Requires strong self-consistency per key (same as Sui's OwnedLock):
/// a read must atomically see the latest write. Cross-key consistency
/// is NOT required (enabling per-cell sharding).
pub type CellLockTable = HashMap<(CellId, u64), CellLockEntry>;
```

### Integration Points

1. **Node turn submission API** (`node/src/api.rs`): After receiving a turn, call `is_fast_path_eligible`. If eligible, call `process_fast_path_lock` instead of forwarding to Morpheus. Return the TurnSign to the client.

2. **Federation gossip** (`node/src/federation_sync.rs`): Add a new gossip topic `pyana/fast-path/signs` for broadcasting TurnSign messages between the client/gateway and validators.

3. **Block processing loop**: Call `expire_stale_locks` at each block. Call `clear_all_locks` at epoch boundary (detected via `is_epoch_boundary` from `federation/src/epoch.rs`).

4. **Consensus-path interaction**: Before forwarding a turn to Morpheus, acquire CellLocks for all owned cells in the write set (same as `process_fast_path_lock` but without returning a TurnSign). This prevents fast-path/consensus-path conflicts on the same cell.

5. **BudgetGate refund**: The `expire_stale_locks` function calls `budget_gate.fast_unlock(fee, &digest)` for each expired lock, restoring the tentative debit to the silo's slice.

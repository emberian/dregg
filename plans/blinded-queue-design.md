# Blinded Queue Design

Applying the note spending pattern to queues so the network (relay/executor) does not learn which element was consumed.

## 1. Model

A **blinded queue** stores commitments rather than plaintext entries. Consumers prove knowledge of a committed element without revealing which one.

**Current MerkleQueue** (`storage/src/queue.rs`):
- Stores `QueueEntry` with plaintext `content_hash`, `sender`, `deposit`, `enqueued_at`, `size`
- Dequeue takes the HEAD element (FIFO, position known to everyone)
- The operator sees exactly which entry was consumed and by whom

**Blinded queue**:
- Enqueue: sender computes `commitment = Poseidon2(message || randomness)` and posts `(commitment, deposit)` to the queue
- Consume: consumer publishes `nullifier = Poseidon2(commitment || secret || queue_position_or_nonce)` plus a STARK proof
- The operator sees commitments in, nullifiers out; cannot link them

### What the operator learns

| Observable | Blinded queue | Current queue |
|---|---|---|
| Queue length | Yes | Yes |
| Enqueue timing | Yes | Yes |
| Consumption timing | Yes | Yes |
| Total flow (in/out counts) | Yes | Yes |
| WHICH commitment was consumed | **No** | Yes |
| Message content | **No** | No (already hashed) |
| Consumer identity | **No** | Yes (via dequeue order) |

### What the consumer proves

1. "I know the preimage of SOME commitment in this queue's Merkle tree"
2. "This nullifier is correctly derived from that commitment + my secret"
3. "This nullifier has not been published before (freshness)"

This is **exactly** NoteSpendingAir applied to the queue's commitment tree instead of the note tree.

## 2. Circuit: Reusing NoteSpendingAir

The existing NoteSpendingAir (`circuit/src/note_spending_air.rs`) proves:
- Commitment preimage knowledge: `commitment = poseidon2(owner, value, asset_type, creation_nonce, randomness)`
- Nullifier derivation: `nullifier = poseidon2(commitment, spending_key[0..8], creation_nonce)`
- Merkle membership: commitment is in a tree with a given root (Poseidon2 Merkle path, 4-ary)

For a blinded queue consumption, we map:

| NoteSpendingAir concept | Blinded queue concept |
|---|---|
| `owner` | Unused (or: recipient identity commitment) |
| `value` | Unused (or: deposit amount) |
| `asset_type` | Queue type tag |
| `creation_nonce` | Enqueue nonce (unique per entry) |
| `randomness` | Blinding factor chosen by sender |
| `spending_key[0..8]` | Consumer's secret (248-bit) |
| Merkle tree | Queue commitment tree (same Poseidon2 4-ary Merkle) |
| `nullifier` (public input) | Queue consumption nullifier |
| `merkle_root` (public input) | Queue tree root at consumption time |

### Public inputs for queue consumption proof

```
[nullifier, queue_tree_root, queue_type_tag, deposit_amount_or_zero]
```

The verifier checks:
- `nullifier` is fresh (not in the queue's nullifier set)
- `queue_tree_root` matches the current queue state
- The STARK proof verifies

### Circuit cost

- Width: 19 columns (same as NoteSpendingAir)
- Rows: 1 + depth (depth = log4 of queue capacity; depth-4 supports 256 entries, depth-8 supports 65536)
- Trace padded to next power of 2
- Proof size: ~1.5-3 KiB (same as note spending proofs)
- Proving time: <100ms for depth-4 on modern hardware

No new circuit is needed. We instantiate the DSL version (`circuit/src/dsl/note_spending.rs`) pointed at the queue tree.

## 3. The Ordering Tradeoff

### Unordered consumption (the straightforward case)

In a blinded queue, the consumer proves "I know the preimage of SOME element" without revealing which. This means any element can be consumed in any order.

**This is NOT FIFO.** It is a "consume-any" set.

**When acceptable:**
- Capability inbox (CapInbox): recipient reads messages in any order. The inbox is already used like a mailbox, not a strict FIFO pipeline.
- Anonymous voting: consume your vote token in any order relative to other voters.
- Private messaging: read messages in any order.
- Sealed-bid auctions: bids are consumed (revealed) independently.

**When NOT acceptable:**
- Ordered processing queues (job queues where task 1 must complete before task 2)
- Priority queues
- Consensus sequencing

### Ordered variant (much harder)

To enforce FIFO while maintaining blindness, you must prove: "I consumed the element at position 0 (the head)" without revealing which commitment sits at position 0.

This requires the queue structure itself to commit to ordering while hiding individual contents. Approach:

1. The queue maintains a Merkle tree where leaf ORDER is committed (leaves are indexed)
2. The consumer proves: "The leaf at index `head_pointer` has commitment C, and I know the preimage of C"
3. The `head_pointer` value is a public input (everyone sees the queue advancing), but the COMMITMENT at that position is not revealed

This needs a different circuit:
- Public inputs: `[nullifier, queue_root, head_pointer]`
- Witness: commitment at `head_pointer`, preimage, Merkle path for position `head_pointer`
- Constraint: leaf at `head_pointer` in the tree = commitment; preimage matches; nullifier derived correctly

This reveals WHICH POSITION was consumed (always the head), but NOT which commitment was at that position. The privacy is weaker: the operator knows "position 0 was just consumed" but doesn't know what content was there.

**Assessment:** The ordered variant is viable but provides less privacy (position is public). For the inbox use case, unordered consumption is superior because it leaks less.

## 4. Deposit Handling

Current system: sender pays `deposit` on enqueue, refunded (90%) on GC or consumed by the owner on read.

### Problem with blinding

When a commitment is consumed via nullifier:
- The consumer reveals nothing about their identity
- Who receives the deposit refund?

### Options

**Option A: Deposit embedded in commitment, claimed by consumer**

The deposit is part of the commitment preimage: `commitment = Poseidon2(message || randomness || deposit_amount)`. The consumer's proof reveals `deposit_amount` as a public input. The executor credits `deposit_amount` to... where?

Sub-option A1: The consumer provides a fresh stealth address as part of the consumption proof's public inputs. The deposit goes there. This reveals a destination address (albeit a one-time stealth address).

Sub-option A2: The deposit creates a new blinded note (commitment) in the note tree, spendable later by the consumer.

**Option B: Deposit stays with the queue operator (no refund)**

The deposit is purely anti-spam. On consumption, the deposit is burned or goes to the queue owner. Simplest approach. The deposit amount is public metadata on the commitment (visible at enqueue time).

**Option C: Deposit refunded to sender on consumption**

Since the sender is known (they posted the commitment publicly), the executor can refund the deposit to the sender's quota when the corresponding nullifier appears. But this requires the operator to know which commitment was consumed -- breaking the privacy model.

**Recommendation: Option B for simplicity.**

The deposit is anti-spam. The queue owner keeps it as compensation for hosting. The consumer gets the MESSAGE value, not the deposit. This aligns with the current inbox model where the owner collects deposits as compensation for inbox storage.

If deposit refund to the sender is required, use Option A2: the consumption proof emits a new note commitment for the deposit amount, which the sender can later claim via their own note spending proof. This requires the sender to have provided a "refund key" embedded in the original commitment.

## 5. Interaction with Programmable Queue Constraints

### ACL (authorized senders)

Current: `CapInbox` checks nothing about sender identity beyond the deposit.

Blinded: To restrict WHO can enqueue, require a ring membership proof at enqueue time:
- Sender proves "I am one of the N authorized senders" via ring membership (same as blinded presentation proof in `circuit/src/presentation.rs`)
- The ring is the set of authorized sender public keys
- Proof: STARK proving Merkle membership in the authorized-senders tree without revealing which sender

### Rate limiting

Current: Not implemented at the queue level (could check sender identity).

Blinded: Use epoch-scoped nullifiers (same pattern as `intent/src/lib.rs` `compute_stake_nullifier`):
- Each sender gets K nullifiers per epoch
- On enqueue, sender must publish a "sender epoch nullifier" proving they haven't exceeded K enqueues this epoch
- The operator sees nullifiers but cannot link them to specific senders (different nullifiers per epoch = unlinkable across epochs)

### Deposit minimum

This can remain unchanged. The deposit is public metadata attached to the commitment. The queue rejects enqueues below the minimum deposit regardless of blinding.

### Message size limits

Currently checked against `max_message_size`. In a blinded queue, the MESSAGE itself is committed (not stored in plaintext). The queue stores only the commitment (32 bytes). Actual message size constraints would need to be proven in the enqueue proof, or the queue simply bounds the number of commitments (capacity) rather than byte size.

## 6. Implementation Sketch

### Types

```rust
/// A commitment posted to a blinded queue.
pub struct BlindedQueueCommitment {
    /// Poseidon2(message_fields || randomness) - the committed value.
    pub commitment: BabyBear,
    /// Deposit paid by sender (public, anti-spam).
    pub deposit: u64,
    /// When this was enqueued (block height).
    pub enqueued_at: u64,
}

/// The blinded queue state.
pub struct BlindedQueue {
    /// Poseidon2 Merkle tree of commitments.
    commitment_tree: Poseidon2MerkleTree,
    /// Nullifier set (tracks consumed entries).
    nullifiers: NullifierSet,
    /// Queue capacity.
    capacity: usize,
    /// Total entries enqueued (monotonic counter).
    total_enqueued: u64,
    /// Total entries consumed (monotonic counter).
    total_consumed: u64,
    /// Minimum deposit.
    min_deposit: u64,
}

/// Witness for consuming a blinded queue entry.
/// This is exactly NoteSpendingWitness with queue-specific semantics.
pub struct BlindedConsumeWitness {
    /// Fields that hash to the commitment (application-specific).
    pub message_fields: Vec<BabyBear>,
    /// Blinding randomness used at enqueue time.
    pub randomness: BabyBear,
    /// Consumer's secret key (248-bit, 8 BabyBear limbs).
    pub consumer_secret: [BabyBear; 8],
    /// Merkle path in the queue's commitment tree.
    pub merkle_siblings: Vec<[BabyBear; 3]>,
    /// Merkle path positions.
    pub merkle_positions: Vec<u8>,
}

/// Public result of a blinded consumption.
pub struct BlindedConsumeResult {
    /// The nullifier (published, prevents double-consume).
    pub nullifier: BabyBear,
    /// The queue tree root this proof is valid against.
    pub queue_root: BabyBear,
    /// The STARK proof of valid consumption.
    pub proof: StarkProof,
}
```

### Methods

```rust
impl BlindedQueue {
    /// Enqueue: add a commitment to the tree.
    /// Caller computes commitment externally and posts it.
    pub fn enqueue(&mut self, commitment: BabyBear, deposit: u64) -> Result<(), QueueError>;

    /// Verify a consumption proof and record the nullifier.
    pub fn consume(&mut self, result: &BlindedConsumeResult) -> Result<(), ConsumeError>;

    /// Current tree root (needed by consumers to build proofs).
    pub fn root(&self) -> BabyBear;

    /// Number of entries (committed - consumed).
    pub fn pending_count(&self) -> u64;

    /// Generate a Merkle proof for a given leaf index (used by the consumer
    /// who knows their commitment's position from the enqueue receipt).
    pub fn prove_membership(&self, index: usize) -> Option<Poseidon2MerkleProof>;
}
```

### Consumption flow

1. **Sender enqueues**: computes `commitment = poseidon2(msg_fields || randomness)`, posts `(commitment, deposit)` to the queue. Receives back: leaf index (their position in the tree).

2. **Consumer prepares**: Consumer knows the message preimage (received off-band or is the intended recipient). They:
   - Look up the current `queue_root`
   - Obtain the Merkle proof for their commitment's leaf index
   - Compute `nullifier = poseidon2(commitment || consumer_secret || nonce)`
   - Generate STARK proof via `prove_note_spend_dsl` (pointed at queue tree)

3. **Consumer submits**: Posts `(nullifier, queue_root, proof)` to the executor.

4. **Executor verifies**:
   - `queue_root` matches current or recent queue state
   - `nullifier` is not in the nullifier set
   - STARK proof verifies against `(nullifier, queue_root)` as public inputs
   - Records nullifier, increments consumed count

5. **Executor does NOT learn**: which commitment was consumed, what the message said, or who consumed it.

## 7. Blinded CapInbox: The Primary Use Case

The `CapInbox` (`storage/src/inbox.rs`) is the ideal candidate:
- Alice receives `HandoffCertificate`s, `SturdyRef`s, encrypted messages
- The relay/executor currently sees which message Alice reads next (FIFO order reveals timing)
- With a blinded inbox, Alice proves "I consumed some message from my inbox" without the relay learning which

### Migration path

```
CapInbox (current, plaintext)
    |
    v
BlindedCapInbox (new)
    - enqueue: sender encrypts message to Alice's view key,
      computes commitment = Poseidon2(encrypted_ciphertext_hash || randomness),
      posts (commitment, deposit)
    - consume: Alice proves knowledge of preimage, publishes nullifier
    - Alice decrypts the actual message offline (she has the ciphertext
      from the gossip layer or a side-channel)
```

### What changes for senders

Senders must:
1. Encrypt their message to the recipient's view key (already done for `InboxMessage::Encrypted`)
2. Compute a Poseidon2 commitment over the message hash + randomness
3. Post the commitment (not the encrypted message itself) to the queue

The encrypted message travels via a separate channel (gossip, direct connection, or stored alongside the commitment in an encrypted blob the executor cannot read).

### What changes for the recipient

The recipient must:
1. Maintain a local index of which commitments in their inbox correspond to which messages (they receive the plaintext mapping off-band)
2. When ready to "acknowledge" consumption, generate a STARK proof and publish the nullifier
3. The actual message reading happens offline (the recipient has the decryption key)

**Key insight:** In the blinded model, "consuming" from the queue is not the same as "reading" the message. The recipient may have already read the message via the encrypted side-channel. The consumption proof is an ACKNOWLEDGMENT that frees up queue capacity and triggers deposit handling.

## 8. Use Cases and Non-Use-Cases

### When blinded queues are useful

| Use case | Why blinding helps |
|---|---|
| Capability inbox | Relay doesn't learn which handoff cert Alice acknowledged |
| Anonymous voting | Ballot box: votes are committed, voter consumes their vote-token via nullifier |
| Private messaging | Messages committed, recipient proves consumption without revealing which |
| Sealed-bid auctions | Bids committed, revealed only when consumed (auction ends) |
| Witness coordination | Parties prove they received a coordination message without revealing sequence |

### When blinded queues are NOT useful (overkill)

| Use case | Why blinding is unnecessary |
|---|---|
| Public event streams (pub-sub) | Everyone reads everything; no consumption privacy needed |
| Work queues (job dispatch) | Consumer identity and consumption order are public by design |
| Admin/operator queues | The admin IS the operator; hiding from yourself is pointless |
| Audit logs | The entire point is public observability |
| Consensus message queues | Validators must attribute messages for BFT protocol correctness |

## 9. Open Questions

1. **Commitment expiry / GC**: In the current queue, expired entries are GC'd by the operator (who can see timestamps). In a blinded queue, the operator knows `enqueued_at` (public metadata) but NOT whether the entry has been consumed (only nullifiers tell that). GC must compare the nullifier set against the commitment set -- but without knowing which nullifier maps to which commitment. Resolution: the operator GCs by age only (evict commitments older than TTL regardless of consumption status). Already-consumed commitments whose nullifiers are published can be pruned from the tree.

2. **Queue root freshness**: If the queue tree changes between when the consumer obtained their Merkle proof and when they submit the consumption proof, the root won't match. Resolution: accept proofs against any root from the last N blocks (a "root history" window, similar to how note trees work with attested roots).

3. **Consumer must know their leaf index**: The consumer needs to know WHERE in the tree their commitment lives to generate the Merkle proof. This means either (a) the sender tells the recipient the index at send time, or (b) the recipient scans all commitments to find theirs (they can trial-decrypt or trial-hash to identify their entries). For encrypted inboxes, (b) is natural: recipient tries to decrypt each commitment's associated ciphertext.

4. **Nullifier linkability across queues**: If the same consumer secret is used across multiple queues, nullifiers could potentially be correlated. Resolution: derive per-queue secrets -- `queue_secret = poseidon2(master_secret || queue_id)`. Different queues produce different nullifiers for the same underlying message.

5. **Sender-consumer separation**: In the note model, the spender (consumer) is the note owner. In a queue, the SENDER creates the commitment but the CONSUMER (recipient) consumes it. The consumer needs a secret that was embedded at commitment time. Two designs:
   - (a) Sender and consumer share a secret (Diffie-Hellman: sender uses recipient's public key to derive shared randomness). Consumer can then derive the nullifier.
   - (b) Sender embeds the consumer's public key in the commitment. Consumer proves knowledge of the corresponding private key. This is the natural fit for the inbox model (sender knows the recipient's address).

6. **Batch consumption**: Can multiple entries be consumed in a single proof? Yes, via the IVC/multi-step framework (`circuit/src/ivc.rs`). Each consumption is one step in a fold chain. The final proof attests to N consumptions. This amortizes verification cost.

7. **Interaction with backpressure**: The current `CapInbox` enforces backpressure (minimum reads per epoch). In a blinded queue, the operator can still count nullifiers published per epoch. If fewer than `min_reads` nullifiers appear, backpressure triggers eviction of the oldest commitments (by `enqueued_at` timestamp, which is public).

## 10. Security Properties

- **Unlinkability**: No observer can link a nullifier to a specific commitment (requires breaking Poseidon2 preimage resistance)
- **Double-consume prevention**: Each commitment produces exactly one valid nullifier; the nullifier set prevents replay
- **Freshness**: Queue root history window prevents stale proofs while allowing slight delays
- **Anti-spam**: Deposits remain public and enforced at enqueue time
- **Soundness**: Consumption proof is a STARK -- computationally sound with ~100-bit security (BabyBear field, standard FRI parameters)

## 11. Relationship to Existing Infrastructure

| Component | Role in blinded queues |
|---|---|
| `NoteSpendingAir` / DSL version | The consumption proof circuit (reused directly) |
| `Poseidon2MerkleTree` (`commit/`) | Queue commitment tree storage |
| `NullifierSet` pattern (`cell/src/note.rs`) | Tracks consumed queue entries |
| `StakeProof` / epoch nullifiers (`intent/src/lib.rs`) | Rate-limiting blinded enqueue |
| `BlindedPresentationProof` (`circuit/src/presentation.rs`) | ACL enforcement (ring membership for authorized senders) |
| `CapInbox` (`storage/src/inbox.rs`) | Primary consumer of this design (blinded inbox variant) |

No new circuits required. The entire mechanism is a re-parameterization of existing note spending infrastructure pointed at a queue-specific Merkle tree.

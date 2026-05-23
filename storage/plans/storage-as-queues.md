# Storage Blobs as Rentable Message Queues

## Core Insight

Storage blobs are general-purpose rentable space. A "file" and a "message queue" and
a "capability inbox" are all the same underlying primitive: a quota-bounded, metered,
content-addressed blob whose interpretation depends on the overlay protocol.

The storage crate already has all the economic machinery (quotas, computron metering,
per-epoch rental, refund-on-delete, TTL-based relay pricing). What's missing is
**structured blob types** that layer queue semantics on top of the existing
ContentStore + SpaceBank.

---

## 1. Message Queue as a Storage Blob

### Data Structure: MerkleQueue

A queue is an append-only log with a read cursor, stored as a Merkle tree over its
entries. The queue state is fully described by:

```rust
/// A provable append-only message queue backed by a storage blob.
pub struct MerkleQueue {
    /// Quota cell that owns this queue's storage.
    pub owner: QuotaId,
    /// Current Merkle root of all enqueued messages (the queue's content address).
    pub root: ContentHash,
    /// Total messages enqueued (append index).
    pub tail: u64,
    /// Read cursor (first unread message index).
    pub head: u64,
    /// Maximum capacity in bytes (derived from quota allocation).
    pub capacity_bytes: u64,
    /// Current bytes used.
    pub used_bytes: u64,
    /// Overflow policy.
    pub overflow: OverflowPolicy,
}

pub enum OverflowPolicy {
    /// Ring buffer: oldest messages evicted when full.
    RingBuffer,
    /// Reject: new enqueues fail when full (sender gets error).
    Reject,
    /// Grow: auto-expand (charges additional rent from owner's quota).
    Grow { max_bytes: u64 },
}
```

### Merkle Queue Operations

Each operation updates the root hash, making the queue state content-addressed:

- **Enqueue(msg)**: Append leaf `hash(msg)` at position `tail`. Update root via
  Merkle path. Increment `tail`. Charge sender.
- **Dequeue()**: Reveal leaf at `head` + Merkle inclusion proof. Advance `head`.
  Free to reader (already paid by sender).
- **Peek(n)**: Read without advancing cursor. Free.
- **Compact()**: After `head` advances past half the tree, rebuild a smaller tree.
  Owner gets partial refund for freed space.

### Merkle Tree Structure

Use a *sparse binary Merkle tree* where:
- Leaves are `blake3(message_bytes)` at positions `0..tail`
- Interior nodes are `blake3(left_child || right_child)`
- The root IS the content address: `queue.root == ContentStore key`

This means each queue state can be verified by anyone with the root:
- "Message M was enqueued at position P" = Merkle inclusion proof
- "The queue had exactly N messages at state S" = the root encodes this

### Why Not Just Append to a Blob?

Using splice (`ContentStore::splice`) on a flat blob works but:
1. Every append rewrites the entire blob (O(n) cost)
2. No provability of individual messages
3. No efficient inclusion proofs

A Merkle queue gives O(log n) append/prove and the root serves as a succinct
commitment to the entire queue history.

---

## 2. Capability Inbox

### The Problem

When someone sends you a cap (HandoffCertificate, sturdy ref, live ref routing),
it needs to GO somewhere. Currently:

- CapTP's `MessageRelay` (`captp/src/store_forward.rs`) holds messages in-memory
- The relay node bears the storage cost
- No explicit economic relationship between sender and recipient
- Relay capacity limits are ad-hoc (`max_queue_depth`, `max_total_messages`)

### The Solution: Inbox = Your Storage Blob

```rust
/// A capability inbox: a MerkleQueue specialized for incoming cap deliveries.
pub struct CapInbox {
    /// Underlying queue (owned by the inbox holder).
    pub queue: MerkleQueue,
    /// Public key for encryption (senders encrypt to this).
    pub recipient_pk: [u8; 32],
    /// Deposit required from senders (anti-spam, refunded on read).
    pub deposit_per_message: u64,
    /// Deposits held (refundable to recipient when messages are read).
    pub held_deposits: Vec<HeldDeposit>,
}

pub struct HeldDeposit {
    pub sender_quota: QuotaId,
    pub amount: u64,
    pub message_index: u64,
}
```

### Economic Model: Who Pays

1. **Recipient** pays ongoing rental for the inbox blob (per-epoch, proportional to
   `capacity_bytes`). This bounds their spam surface voluntarily.

2. **Sender** pays a deposit to enqueue:
   - Deposit = `deposit_per_message` computrons from sender's quota
   - Deposited into recipient's held_deposits
   - When recipient reads: deposit refunded to recipient (they earned it by
     processing the message)
   - When message expires unread: deposit returned to sender (minus a small
     processing fee)

3. **Anti-spam properties**:
   - Inbox size is bounded by recipient's quota (they choose how much spam to accept)
   - Sending costs the sender real computrons (sybil-resistant)
   - Recipient profits from reading legitimate messages (incentive to stay online)
   - When inbox is full: messages bounce (sender notified immediately)

### Integration with CapTP Store-and-Forward

The existing `MessageRelay` in `captp/src/store_forward.rs` becomes a thin wrapper:

```rust
/// A relay node = "I host your inbox blob as a service"
pub struct StorageBackedRelay {
    /// The underlying storage crate's content store.
    store: ContentStore,
    /// Map from destination public key to their inbox queue ID.
    inboxes: HashMap<[u8; 32], MerkleQueue>,
    /// The metering policy (same as storage crate's MeteringPolicy).
    policy: MeteringPolicy,
}
```

The relay's `enqueue()` becomes: write into the recipient's MerkleQueue (which is
a blob in the ContentStore). The relay's `drain()` becomes: reveal messages from
head to tail with Merkle proofs.

---

## 3. Integration with Effect VM

### New Effects

The Effect VM (`circuit/src/effect_vm.rs`) currently has 18 effect types. Storage
queue operations map cleanly to new effects:

```rust
// Proposed new selectors (indices 18..22)
pub const ALLOCATE_QUEUE: usize = 18;   // Create a new MerkleQueue blob
pub const ENQUEUE_MESSAGE: usize = 19;  // Append message + update root
pub const DEQUEUE_MESSAGE: usize = 20;  // Advance head + reveal message
pub const RESIZE_QUEUE: usize = 21;     // Change capacity (pay more/less rent)
```

### Constraint Design

**AllocateQueue** (effect 18):
- Params: `[capacity_bytes, overflow_policy, deposit_per_message, 0, 0, 0, 0, 0]`
- Constraint: `state_after.balance -= initial_rental_cost(capacity_bytes)`
- Constraint: `state_after.field[queue_slot] = empty_merkle_root`
- The queue root is stored in one of the 8 custom field slots

**EnqueueMessage** (effect 19):
- Params: `[message_hash, target_queue_field_slot, deposit_amount, sender_nonce, 0, 0, 0, 0]`
- Constraint: `new_root = hash(old_root, message_hash, tail_index)` (Merkle append)
- Constraint: `state_after.balance -= deposit_amount` (sender pays deposit)
- Constraint: `tail_after = tail_before + 1`

**DequeueMessage** (effect 20):
- Params: `[expected_hash, merkle_proof_aux[0..5], queue_field_slot, 0]`
- Constraint: `verify_merkle_inclusion(root, head, expected_hash, proof)`
- Constraint: `head_after = head_before + 1`
- Constraint: `state_after.balance += deposit_refund` (recipient collects)

**ResizeQueue** (effect 21):
- Params: `[new_capacity_bytes, 0, 0, 0, 0, 0, 0, 0]`
- Constraint: `state_after.balance -= resize_cost(old_capacity, new_capacity)`

### Trace Layout Consideration

The current trace width is 65 columns. Adding 4 selectors expands to 69 columns
(still fine for BabyBear STARK). The Merkle proof verification in DequeueMessage
needs auxiliary columns for intermediate hash values -- the existing `aux[0..7]`
slots plus `aux[8..10]` (state commitment intermediates) may need expansion to
~15 aux columns for a depth-32 Merkle proof. Alternative: use a depth-16 tree
(64K messages max per queue) which fits in the existing aux budget with batched
hashing.

---

## 4. Merkle Queue: Provability Details

### Hash Function Choice

Use the same hash as the storage crate: **blake3** for the content layer, but
for in-circuit verification use **Poseidon2** (already available via
`circuit/src/poseidon2`). The queue maintains dual commitments:

- `content_root`: blake3 Merkle root (for storage addressing, off-chain verification)
- `circuit_root`: Poseidon2 Merkle root (for in-circuit proof of queue operations)

The circuit proves Poseidon2 operations. A one-time binding proof shows that the
blake3 root and Poseidon2 root commit to the same leaf set (done at queue
creation and after each batch of operations).

### Proof Statements

Each queue operation produces a provable statement:

1. **EnqueueProof**: "Given queue state with root R and tail T, appending message
   with hash H produces new root R' with tail T+1"
2. **DequeueProof**: "Given queue state with root R and head H, the message at
   position H has hash M (with Merkle path), and advancing head produces state
   with head H+1"
3. **QueueIntegrityProof**: "Queue with root R has exactly T-H pending messages,
   all of which are valid Merkle leaves"

These compose with the Effect VM's existing proof machinery: a turn that enqueues
3 messages produces a STARK proving the 3 EnqueueMessage effects, which rolls up
into the IVC chain.

---

## 5. Economic Model Summary

### Cost Table

| Operation | Who Pays | Cost Formula | Refund |
|-----------|----------|--------------|--------|
| Create queue | Owner | `base_cost + capacity * cost_per_byte` | 80% on delete |
| Rent (per epoch) | Owner | `used_bytes * rental_cost_per_byte_epoch` | N/A |
| Enqueue | Sender | `deposit + msg_size * cost_per_byte` | Deposit to recipient on read |
| Dequeue | Recipient | Free (already paid by sender) | Collects deposit |
| Resize (grow) | Owner | `delta_bytes * cost_per_byte` | 80% on shrink |
| Message expires | N/A | Deposit returned to sender (minus 10% fee) | N/A |
| Queue GC'd | N/A | Owner's quota exhausted; all messages lost | N/A |

### Incentive Alignment

- **Recipients** are incentivized to stay online and process messages (they collect
  deposits).
- **Senders** are incentivized to send only to live recipients (deposits are locked
  until read or expired).
- **Relay operators** are incentivized to host inboxes (they collect hosting fees =
  the per-epoch rental from owners, which is a service they provide).
- **The system** is incentivized toward cleanup (refund-on-delete, deposit recovery,
  GC of unfunded queues).

### GC Integration

When `SpaceBank::tick_epoch()` finds a depleted quota:
1. The queue owner's quota is exhausted
2. All their queue blobs become eligible for GC
3. Held deposits on unread messages are returned to senders (minus processing fee)
4. The queue root is tombstoned (can be verified as "existed but was evicted")
5. Relay node reclaims the storage

This composes with the existing `tick_epoch() -> Vec<QuotaId>` mechanism in
`storage/src/quota.rs`.

---

## 6. Relationship to Ensue (o1-Labs)

The Ensue project (o1-labs/ensue-whitepaper) addresses verified data availability
using Mina-compatible proof systems. Key concepts that apply here:

### Relevant Ideas (inferred from project structure and o1-labs' DA work)

1. **Proof-of-Retrievability via Sampling**: Ensue uses erasure coding + random
   sampling to prove data availability without downloading everything. Our
   `storage/src/erasure.rs` already implements this pattern. For queues: the
   queue blob can be erasure-encoded so light clients can verify "this inbox
   exists and has data" without downloading all messages.

2. **KZG/Polynomial Commitments for Ordered Data**: Ensue likely uses polynomial
   commitments (building on `poly-commitment/src/kzg.rs` in proof-systems) to
   commit to ordered sequences. For queues: instead of a Merkle tree, you could
   commit to the queue as a polynomial where `p(i) = message_hash[i]`. Opening
   at point `i` proves message `i` was enqueued. This is more efficient for
   batch proofs but harder to do incrementally.

3. **Economic Availability Guarantees**: The key Ensue insight is that storage
   providers post bonds (staked collateral) that are slashed if they cannot
   produce requested data. For our relay model: relay operators could post an
   obligation (via `CreateObligation` effect) that gets slashed if they fail to
   serve a requested message within the TTL window.

4. **Recursive Proofs of Storage**: Ensue builds on Mina's recursive SNARKs to
   maintain a rolling proof that "all committed data is still available." For
   pyana: the IVC chain already provides recursive proofs. A queue's integrity
   can be part of the recursive state: "at block N, queue Q has root R with
   T messages, and all messages from head to tail are retrievable."

### What We Can Reuse from proof-systems/

The `proof-systems/` checkout is o1-labs' Kimchi/Pickles infrastructure:
- **Poseidon sponge** (`poseidon/src/sponge.rs`): Already integrated via our
  `circuit/src/poseidon2` module. Use for in-circuit Merkle hashing.
- **Polynomial commitments** (`poly-commitment/src/commitment.rs`): The KZG and
  IPA commitment schemes could back a vector-commitment-based queue (alternative
  to Merkle tree). KZG gives O(1) proofs of "message at index i" but needs a
  trusted setup.
- **Arrabbiata IVC** (`arrabbiata/`): Nova-style folding for recursive queue
  integrity proofs. Our existing IVC chain already handles this.

The main reuse opportunity is the Poseidon sponge for in-circuit Merkle operations
and potentially KZG for batch queue proofs in the future.

---

## 7. Integration with Governed Namespace

The governed namespace (`apps/governed-namespace/src/`) already has content-addressed
storage (`storage.rs`). Queues integrate as:

```
/inboxes/{federation_id}    -> CapInbox (your capability inbox)
/queues/{queue_id}          -> MerkleQueue (general purpose)
/relays/{relay_id}/pending  -> relay's hosted inboxes
```

The namespace's governance layer can enforce policies:
- "Inboxes under `/inboxes/` must have minimum deposit of X computrons"
- "Queues under `/queues/public/` are readable by anyone (pub-sub)"
- "Relay nodes must post obligation of Y computrons per hosted inbox"

---

## 8. Concrete Changes to storage/ Crate

### New Module: `storage/src/queue.rs`

```rust
//! Merkle queue: append-only message queue as a content-addressed blob.

pub struct MerkleQueue { ... }
pub struct QueueConfig { ... }
pub struct EnqueueReceipt { ... }
pub struct DequeueReceipt { ... }

impl MerkleQueue {
    pub fn new(owner: QuotaId, config: QueueConfig, bank: &mut SpaceBank) -> Result<Self, StorageError>;
    pub fn enqueue(&mut self, msg: &[u8], sender: &QuotaId, bank: &mut SpaceBank) -> Result<EnqueueReceipt, StorageError>;
    pub fn dequeue(&mut self, bank: &mut SpaceBank) -> Result<DequeueReceipt, StorageError>;
    pub fn peek(&self, index: u64) -> Option<(&[u8], MerkleProof)>;
    pub fn root(&self) -> ContentHash;
    pub fn len(&self) -> u64;
    pub fn is_full(&self) -> bool;
}
```

### New Module: `storage/src/inbox.rs`

```rust
//! Capability inbox: MerkleQueue specialized for incoming cap deliveries.

pub struct CapInbox { ... }
pub struct InboxConfig { ... }

impl CapInbox {
    pub fn new(owner: QuotaId, recipient_pk: [u8; 32], config: InboxConfig, bank: &mut SpaceBank) -> Result<Self, StorageError>;
    pub fn deliver(&mut self, msg: &[u8], sender: &QuotaId, bank: &mut SpaceBank) -> Result<DeliveryReceipt, StorageError>;
    pub fn collect(&mut self) -> Vec<(Vec<u8>, HeldDeposit)>;
    pub fn bounce_full(&self) -> bool;
}
```

### Modifications to Existing Modules

1. **`storage/src/metering.rs`**: Add `StorageOp::Enqueue` and `StorageOp::Dequeue`
   variants with deposit-aware cost computation.

2. **`storage/src/quota.rs`**: Add `SpaceBank::charge_enqueue()` that handles the
   sender-pays-deposit model (charge sender, hold deposit for recipient).

3. **`storage/src/relay.rs`**: Refactor `MeteredRelay` to optionally back onto
   `MerkleQueue` instead of raw `VecDeque<MeteredMessage>`. The existing interface
   stays the same but gains provability.

4. **`storage/src/lib.rs`**: Add `pub mod queue; pub mod inbox;` and new error
   variants (`QueueFull`, `InboxBounced`, `DepositInsufficient`).

### New Module: `storage/src/merkle.rs`

```rust
//! Sparse Merkle tree for provable queue state.

pub struct SparseMerkleTree { ... }
pub struct MerkleProof { ... }

impl SparseMerkleTree {
    pub fn new(depth: usize) -> Self;
    pub fn append(&mut self, leaf: ContentHash) -> (ContentHash, MerkleProof);
    pub fn prove(&self, index: u64) -> Option<MerkleProof>;
    pub fn verify(root: &ContentHash, index: u64, leaf: &ContentHash, proof: &MerkleProof) -> bool;
    pub fn root(&self) -> ContentHash;
}
```

---

## 9. Implementation Phases

### Phase 1: MerkleQueue (storage primitive)
- Implement `storage/src/merkle.rs` (sparse Merkle tree, blake3-based)
- Implement `storage/src/queue.rs` (MerkleQueue over ContentStore)
- Unit tests: enqueue/dequeue/overflow/compaction
- Integrate with existing SpaceBank metering

### Phase 2: CapInbox (capability delivery)
- Implement `storage/src/inbox.rs`
- Deposit model: sender pays, recipient collects
- Integration test: HandoffCertificate -> inbox -> recipient reads
- Wire up to `captp/src/store_forward.rs` as alternative backend

### Phase 3: Effect VM integration
- Add effects 18-21 (AllocateQueue, EnqueueMessage, DequeueMessage, ResizeQueue)
- Implement Poseidon2 Merkle constraints for in-circuit verification
- Expand trace width or batch hash operations to fit aux columns
- STARK proof of queue operations

### Phase 4: Relay-as-hosted-inbox
- Refactor MeteredRelay to use MerkleQueue backend
- Implement relay operator obligation model (bonded hosting)
- GC integration: unfunded queues -> eviction -> deposit returns
- Erasure coding for inbox availability proofs

### Phase 5: Namespace + governance
- Mount inboxes in governed namespace at `/inboxes/{id}`
- Policy enforcement for deposit minimums, capacity limits
- Pub-sub queues (multi-reader) as a separate overlay

---

## 10. Open Questions

1. **Merkle vs. Vector Commitment**: A KZG-based vector commitment gives O(1)
   proofs and O(1) updates (amortized) but needs a trusted setup. Merkle is
   simpler and transparent. Start with Merkle, consider KZG for batch operations
   later.

2. **Encryption at queue level vs. message level**: Currently CapTP encrypts each
   message individually (per `store_forward.rs`). Should the queue itself be
   encrypted (opaque blob) or should individual messages be encrypted within a
   transparent queue structure? Individual encryption is better for selective
   disclosure and partial reads.

3. **Cross-federation queue mirroring**: If your inbox is hosted on relay R, and
   relay R goes down, can another relay reconstruct your queue from erasure
   chunks? This requires the queue blob to be erasure-coded and chunks distributed.
   The `erasure.rs` module already handles this pattern.

4. **Queue as pub-sub**: A MerkleQueue with multiple readers (each with their own
   head cursor) is a pub-sub topic. The owner pays rent, publishers pay enqueue
   deposits, subscribers read for free. This is a natural extension but needs
   multi-cursor tracking.

5. **Deposit denomination**: Should deposits be in computrons (abstract) or in a
   specific token? Computrons are the natural unit since they're what the storage
   crate already meters. External bridges can convert tokens to computrons.

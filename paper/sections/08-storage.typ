// =============================================================================
// Section 8: Storage Economics and Queues
// =============================================================================

= Storage Economics <sec-storage>

== Design Principles

Storage in a distributed capability system differs fundamentally from blockchain state: cells are sovereign (they own their data), storage is metered (ongoing cost, not one-time), and queues are the primary communication primitive (not shared memory). This section formalizes the storage model, queue semantics, and economic mechanisms that sustain long-term operation.

== Space Banks

A _space bank_ is a governance-managed allocation of storage capacity within a reference group. Each group maintains a total storage budget $B_"total"$ (governance-configurable, initially 1 TiB). Space banks partition this budget among cells:

$ B_"total" = sum_(i=1)^n "space_bank"(i)."allocation" $

Cells draw from their assigned space bank. When a cell's usage exceeds its bank allocation, new storage requests enter a queue: the cell must either free existing storage (triggering GC) or request a governance vote to increase its bank allocation.

=== Bank Operations

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    table.header([*Operation*], [*Authorization*], [*Effect*]),
    [Allocate], [Governance vote], [Increase a cell's bank allocation],
    [Transfer], [Both cells consent], [Move allocation between banks],
    [Reclaim], [Governance vote], [Force-shrink an inactive cell's allocation],
    [Split], [Bank owner], [Divide allocation among sub-cells],
  ),
  caption: [Space bank operations. All require proof of authority.],
)

== Computron-Metered Storage

All persistent storage is metered in computrons with ongoing costs:

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, right, left),
    table.header([*Operation*], [*Cost*], [*Rationale*]),
    [Write (per byte, per epoch)], [1 computron], [Ongoing cost for persistent state],
    [Read (per byte)], [0.01 computrons], [Cheap reads encourage verification],
    [MerkleQueue enqueue], [$10 + |"msg"|$ computrons], [Inbox anti-spam],
    [Erasure shard storage], [0.5 computrons/byte/epoch], [Redundancy at half price],
    [Queue program storage], [2 computrons/byte/epoch], [Programs are long-lived],
  ),
  caption: [Storage metering. Costs are governance-adjustable per reference group.],
)

The key distinction from blockchain gas: storage costs are _ongoing_ (per-epoch rent), not one-time. This ensures sustainable operation---storing 1 MiB forever costs the same as storing it for 1000 epochs at the per-epoch rate, with the cost borne continuously by the cell that benefits from the storage.

== MerkleQueue

The `MerkleQueue` is Pyana's fundamental communication primitive: a content-addressed append-only queue where each state has a unique root hash (BLAKE3 Merkle tree of entries).

=== Structure

Each entry in the queue contains:

- *Content hash*: BLAKE3 of the enqueued data (the data itself may be stored off-queue).
- *Sender*: Identity of the enqueueing cell (for deposit refund tracking).
- *Deposit*: Computrons locked by the sender (anti-spam).
- *Enqueued height*: Block height at enqueue time.
- *Size*: Byte count of the referenced data.
- *TTL*: Maximum blocks before expiry.

The queue root is recomputed on every enqueue/dequeue operation, providing a content-addressed snapshot of queue state at any point. This enables:

$ "root"_n = "BLAKE3"("root"_(n-1) || "entry"_n."content_hash") $

=== Operations

- *Enqueue*: Append a leaf. Sender must lock deposit. Queue root updates.
- *Dequeue*: Advance head pointer. Deposit refunded to sender. Queue root updates.
- *Expire*: Entries past TTL are garbage-collected. Deposit is burned (20%) + treasury (80%).
- *Prove membership*: A STARK proof of queue membership proves a message was enqueued at a specific height.

=== Sender-Pays-Deposit Anti-Spam

The deposit formula prevents inbox flooding:

$ "deposit" = "base_fee" + |"msg"| times r_"byte" + "ttl" times r_"block" $

With defaults: $"base_fee" = 100$, $r_"byte" = 0.1$, $r_"block" = 1$. A 1 KiB message with 1000-block TTL costs $approx 1202$ computrons. The deposit is fully refunded when the recipient processes the message. On timeout, the deposit covers the storage cost incurred by the network.

== Programmable Queues

Standard MerkleQueues are FIFO with uniform access. _Programmable queues_ extend this with custom logic:

=== Queue Programs

A queue program is a predicate $P: "Entry" -> {"accept", "reject", "defer"}$ that filters entries before they join the queue. Programs are committed to the queue's metadata (BLAKE3 of program bytecode) and verified by the executor before admission.

Example programs:

- *Priority queue*: Accept entries sorted by deposit amount (highest first dequeue).
- *Rate limiter*: Accept at most $k$ entries per sender per epoch.
- *Type filter*: Accept only entries whose content hash matches a schema commitment.
- *Auction queue*: Accept bids during a window, sort by value, dequeue winner first.

=== Dataflow Pipelines

Programmable queues compose into dataflow pipelines: the output of one queue feeds the input of another. Each stage applies its program, producing a multi-stage processing pipeline:

$ Q_1 arrow.r^(P_1) Q_2 arrow.r^(P_2) Q_3 arrow.r^(P_3) "cell" $

Pipeline composition is declarative: a cell specifies its intake pipeline as a sequence of queue IDs and programs. The federation ensures causal ordering across pipeline stages.

== Blinded Queues (Fair Unique Withdrawal)

A _blinded queue_ extends MerkleQueue with privacy guarantees for fair withdrawal---no party (including the queue operator) can predict withdrawal order or correlate depositor with withdrawer.

=== Construction

+ *Deposit phase*: Depositors commit entries using Pedersen commitments: $C = g^v h^r$ where $v$ is the entry value and $r$ is blinding randomness.
+ *Shuffle phase*: A verifiable shuffle (provable in STARK) permutes the committed entries. The shuffle proof demonstrates that the output set is a permutation of the input set without revealing the permutation.
+ *Withdrawal phase*: Withdrawers present a STARK proof of knowledge of the opening $(v, r)$ for some entry in the shuffled set, plus a nullifier $nu = "Poseidon2"(v || r || "nonce")$ to prevent double-withdrawal.

=== Properties

- *Fairness*: No party can determine withdrawal order (shuffle is random).
- *Uniqueness*: Each entry can be withdrawn exactly once (nullifier prevents double-spend).
- *Privacy*: Depositor-withdrawer correlation is broken by the shuffle.
- *Verifiability*: The shuffle proof is publicly verifiable; no trusted shuffler.

Applications: fair airdrops (recipients cannot front-run), lottery payouts, anonymous voting (ballot box as blinded queue), and fair NFT minting order.

== Relay Operators

Relay operators provide store-and-forward infrastructure for cells that are intermittently online. A relay:

- Maintains MerkleQueue inboxes for subscribed cells.
- Accepts enqueue operations from senders (collecting deposits).
- Delivers messages when the recipient connects.
- Earns relay fees (a fraction of the sender's deposit, governance-configurable).

=== Relay Economics

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, right, left),
    table.header([*Revenue Source*], [*Share*], [*Trigger*]),
    [Relay fee], [10% of deposit], [On successful delivery],
    [Expired cleanup], [5% of burned deposit], [On TTL expiry],
    [Erasure shard hosting], [Storage rate], [Per-epoch for hosted shards],
    [Cross-group forwarding], [Per-message], [When routing between groups],
  ),
  caption: [Relay operator revenue model. Operators earn from active participation.],
)

Relay operators compete on reliability (uptime), latency (delivery speed), and capacity (queue depth). Cells choose relays via reputation (receipt-chain-based track record) or direct peering agreements.

== State Lifecycle and Deep Garbage Collection

Cell storage follows a lifecycle with automatic transitions:

=== Lifecycle Phases

+ *Birth*: Cell created, initial storage allocation from space bank.
+ *Active*: Cell regularly produces turns. Storage metered at standard rate.
+ *Decay*: No turns for $d_"decay"$ epochs. Storage rate increases linearly (incentivizing cleanup).
+ *Forced sovereignty*: No turns for $d_"force"$ epochs. The federation stops hosting the cell's MerkleQueues. The cell must self-host or lose inbox service.

=== Storage Rent

Active cells pay rent per epoch proportional to their storage usage:

$ "rent"_e = sum_(o in "objects") |o| times r_"base" times cases(1 &"if active", 1 + (e - e_"last") / d_"decay" &"if decaying") $

where $e$ is the current epoch, $e_"last"$ is the epoch of the cell's last turn, and $d_"decay"$ is the decay onset threshold. Rent is deducted from the cell's balance automatically at epoch boundaries.

=== Epoch Rotation

Every $E_"rotation"$ epochs (governance-configurable, default 1000), the storage layer performs a rotation:

- Expired queue entries are garbage-collected (deposits burned/returned).
- Decaying cells have their storage rent increased.
- Cells that have reached forced sovereignty have their relay services terminated.
- Erasure shards are re-verified (challenge-response against committed shard roots).
- Space bank utilization metrics are published for governance decisions.

== Erasure Coding for Data Availability

Sovereign cells maintain their own state, but may opt into _erasure-coded availability_ for their MerkleQueue inboxes:

The state is encoded as $k$-of-$n$ Reed-Solomon shards distributed across reference group nodes:

- *Data availability*: Any $k$ shards reconstruct the full queue state. No single node holds enough to read the content alone (combined with encryption).
- *Reduced per-node cost*: Each node stores $1\/n$ of the data rather than a full copy.
- *Proof of storage*: Nodes periodically prove they still hold their shard via random leaf queries against a committed shard Merkle root.
- *Half-price rate*: Erasure-coded storage costs $0.5times$ the standard rate (redundancy amortized across shards).

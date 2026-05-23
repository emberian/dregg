// =============================================================================
// Section 7: Economic Model
// =============================================================================

= Economic Model

== Fee Model

=== Two-Phase Execution (Mina-Style)

Fees are processed in two phases: (1) the agent's balance is decremented by `turn.fee` and nonce incremented---this is never rolled back; (2) the call forest executes, with effects rolling back on failure but the fee retained. This ensures the federation is compensated for processing regardless of execution outcome.

=== Fee Distribution

Fees are split into three destinations on every committed turn:

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, center, left),
    table.header([*Destination*], [*Share*], [*Rationale*]),
    [Block proposer], [50%], [Direct incentive to process turns],
    [Federation treasury], [30%], [Governance-directed spending],
    [Burned], [20%], [Mild deflation, aligns holder interests],
  ),
  caption: [Fee distribution split. Parameters are governance-adjustable via `FeePolicy` attested at epoch boundaries.],
)

The treasury is a distinguished cell whose spending requires a governance vote (quorum of current committee). This provides sustainable funding for development and operations without external revenue dependencies.

=== Fee Market (EIP-1559 Adaptation)

A base fee adjusts per-block to target 50% utilization:

$ "base_fee"_(n+1) = "base_fee"_n dot (1 + ("actual" - "target") / "target" dot 0.125) $

With parameters: target 1M computrons/block, max 2M, minimum base fee 1, maximum 1000. Users specify `max_fee` and `priority_fee`. They pay $min("max_fee", "base_fee" + "priority_fee")$. The base fee portion follows the standard split; the priority fee goes entirely to the block proposer.

== Validator Staking

=== Deposit-Based Committee Membership

Federation committees are small (3--20 nodes). Rather than heavy proof-of-stake machinery, Pyana uses deposit-based membership:

- Joining requires locking a deposit note with value $>=$ `MINIMUM_VALIDATOR_STAKE` (initially 100,000 computrons)
- The deposit is proven via a STARK range proof (value hidden, threshold satisfaction proven)
- Deposit is locked for the epoch duration + unbonding period (2 epochs)

=== Slash Conditions

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, center, left),
    table.header([*Condition*], [*Slash Amount*], [*Rationale*]),
    [Equivocation (double-vote)], [100%], [Always intentional],
    [Inactivity (>50% missed)], [5% per epoch], [Graceful for maintenance],
    [Invalid attestation], [50%], [Fraud proof required],
  ),
  caption: [Slash conditions. Slashed funds go to the federation treasury (not reporter) to prevent slash-for-profit griefing.],
)

=== Privacy-Compatible Staking

Note values are private (Poseidon2 commitments). Staking uses range proofs: "prove my stake >= X" without revealing the exact value. The `RangeProofAir` decomposes $"value" - "threshold"$ into BabyBear-width bit limbs, proving all are 0/1.

For slashing with private stakes: at deposit time, the validator provides a _slash commitment_ $= "Poseidon2"("note_commitment", "slash", "randomness")$. On slash, the protocol publishes this commitment to a "slashed set." The validator's note is encumbered---spending requires proving non-membership in the slashed set. Slashing is enforced at spend-time (like a lien), not at slash-time.

== Anti-Griefing

=== Conditional Turn Deposits

Conditional turns occupy space in the pending pool until timeout. A reservation deposit makes griefing expensive:

$ "deposit" = "base_deposit" + "per_block_rate" times ("timeout" - "submitted_at") $

With `base_deposit = 500` and `per_block_rate = 10`: a 1000-block conditional costs 10,500 computrons if it times out. On successful execution, the deposit is fully refunded. On timeout, 20% is burned and 80% goes to treasury.

=== Sybil Resistance

Each note commitment can be used as a stake proof $K$ times per epoch (governance parameter, initially $K = 5$). Epoch-scoped stake nullifiers prevent unlimited reuse:

$ "stake_nullifier" = "Poseidon2"("note_commitment", "epoch", "usage_counter") $

The federation maintains an append-only stake nullifier set per epoch. An entity with $N$ notes gets $N times K$ identities per epoch. Privacy is preserved: nullifiers do not reveal which note, and cross-epoch usage is unlinkable.

== Intent Marketplace Economics

=== Fulfiller Fees

When a fulfillment is accepted, the requester pays the fulfiller a `fulfillment_fee` negotiated off-protocol. This is a direct transfer between cells---not mediated by the federation.

=== Priority Tips

Intents can include a `priority_tip` (additional computrons locked with the intent). Higher-tip intents are propagated more eagerly by gossip relays. On fulfillment, the tip goes to the fulfiller. On expiry, the tip is returned minus a `gossip_rent` proportional to time-in-pool.

=== Proof Generation Costs

Proof generation is local (not metered by the network). The cost is borne by the prover in CPU time. Fulfillers factor this into their fulfillment fee. No on-chain "gas for proofs"---the market prices it.

== Incentive Analysis

=== Nash Equilibrium for Validators

With the proposed parameters, honest validation is the dominant strategy whenever annual fee income exceeds server cost plus opportunity cost of stake. Deviation strategies are strictly dominated:

- *Censor turns*: reduces fee income, risks inactivity slash
- *Include invalid turns*: other validators reject the block
- *Equivocate*: 100% stake slash---strictly dominated for any positive stake
- *Go offline*: 5% slash per epoch, lost income

=== Minimum Viable Economics

Federations are small and purpose-built. A 5-node federation serving a specific application domain (agent marketplace, credential issuance) is viable with modest throughput if operators have aligned interests (they are also users). No inflation needed---validators earn directly from fee distribution.

== Comparison

#figure(
  table(
    columns: (auto, auto, auto, auto),
    align: (left, left, left, left),
    table.header([*Property*], [*Pyana*], [*Cosmos*], [*Mina*]),
    [Committee size], [3--20], [100--175], [$tilde$1000],
    [Fee destination], [50/30/20 split], [Proposer+stakers], [Burned],
    [Staking model], [Deposit + range proof], [Delegated PoS], [Delegated PoS],
    [Privacy of stake], [ZK range proof], [Transparent], [Transparent],
    [Fee market], [EIP-1559 adapted], [First-price auction], [Fixed fees],
    [Inflation], [None], [Yes (5--20%)], [Yes],
    [Treasury], [30% of fees], [Community pool (2%)], [None],
  ),
  caption: [Economic model comparison. Pyana is non-inflationary; validators earn from fees.],
)

The key difference from Cosmos: Pyana does not need inflation because federations are small and operators have aligned interests. Cosmos needs inflation because validator sets are large and operators are pure infrastructure providers.

== Storage Economics <sec-storage-economics>

=== Space Banks

A _space bank_ is a governance-managed allocation of storage capacity within a federation. Each federation maintains a total storage budget (governance-configurable, initially 1 TiB). Space banks partition this budget:

$ "total_capacity" = sum_i "space_bank"(i)."allocation" $

Cells draw from their assigned space bank. Over-allocation triggers a queue: new storage requests wait until existing data is GC'd or the bank's allocation is increased via governance vote.

=== Computron-Metered Storage

All persistent storage is metered in computrons:

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, right, left),
    table.header([*Operation*], [*Cost*], [*Rationale*]),
    [Write (per byte, per epoch)], [1 computron], [Ongoing cost for persistent state],
    [Read (per byte)], [0.01 computrons], [Cheap reads encourage verification],
    [MerkleQueue enqueue], [10 + size computrons], [Inbox anti-spam],
    [Erasure shard storage], [0.5 computrons/byte/epoch], [Redundancy is half-price (amortized across shards)],
  ),
  caption: [Storage metering. Costs are governance-adjustable per federation.],
)

=== MerkleQueue Inboxes

Each cell has a _MerkleQueue inbox_: a Merkle-committed FIFO queue of pending messages. The inbox provides:

- *Sender-pays-deposit anti-spam*: The sender locks a deposit when enqueuing a message. If the recipient processes it, the deposit is refunded. If the message expires (TTL exceeded), the deposit is burned. This makes inbox flooding expensive.
- *Causal ordering*: Messages in the inbox are ordered by their causal position in the Blocklace DAG.
- *Offline delivery*: Messages persist in the inbox until the recipient processes them or they expire. No liveness requirement on the recipient.
- *Provable delivery*: A STARK proof of inbox membership proves a message was delivered at a specific height.

The deposit formula:

$ "deposit" = "base_inbox_fee" + "message_size" times "per_byte_rate" + "ttl_blocks" times "per_block_rate" $

With defaults: `base_inbox_fee = 100`, `per_byte_rate = 0.1`, `per_block_rate = 1`. A 1 KiB message with 1000-block TTL costs $100 + 102.4 + 1000 = 1202.4$ computrons deposit.

=== Erasure Coding for State Availability

Sovereign cells maintain their own state, but may opt into _erasure-coded availability_: the state is encoded as $k$-of-$n$ Reed-Solomon shards distributed across federation nodes. This provides:

- *Data availability without trust*: Any $k$ shards reconstruct the full state. No single node holds enough to read the state alone (combined with encryption).
- *Reduced per-node cost*: Each node stores $1/n$ of the state rather than a full copy.
- *Proof of storage*: Nodes periodically prove they still hold their shard via a challenge-response protocol (random leaf queries against a committed shard Merkle root).

Erasure coding is opt-in and priced at half the per-byte storage rate (the redundancy cost is amortized across the shard set). Cells that self-host exclusively pay zero storage to the federation.

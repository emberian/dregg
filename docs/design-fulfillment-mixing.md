# Fulfillment Mixing and Batching: Breaking Timing Correlation

## Problem

When an intent is posted and a fulfillment appears shortly after, timing correlation reveals who fulfilled it. The current commit-reveal flow (`commit_reveal_fulfillment.rs`) uses a 5-second window with a 60-second commitment expiry. In small anonymity sets (<100 active participants), an observer correlating `commitment_hash` appearance time with the preceding intent post trivially identifies the fulfiller.

Current timing: intent at T, commitment at T+2s, reveal at T+7s, intent removed at T+8s.

## Approaches

### 1. Delay Pool (Batch Release)

Fulfilled intents enter a delay pool; the pool releases all pending fulfillments simultaneously at fixed intervals (e.g., every 30s).

- **Latency**: +15s average (half the batch interval)
- **Anonymity set**: All fulfillers active within one batch window
- **Liveness**: No cooperation needed beyond the pool operator (can be the node itself)
- **Complexity**: Days. Extend `FulfillmentRegistry` with a `pending_reveals: Vec<FulfillmentResult>` flushed on a timer
- **Compatibility**: Direct extension of existing commit-reveal. The reveal phase becomes "reveal into pool" rather than "reveal and broadcast"

### 2. Dummy Traffic (Cover Commitments)

Nodes generate fake `FulfillmentCommitment` messages at a constant rate. Real commitments are indistinguishable until reveal, when fakes produce invalid proofs (discarded silently).

- **Latency**: Zero additional (real fulfillments proceed at normal speed)
- **Anonymity set**: Proportional to dummy rate -- 10 dummies/s with 1 real/30s gives ~300:1
- **Liveness**: Each node generates independently; no coordination
- **Complexity**: Days. Add a `DummyCommitmentGenerator` that produces random `commitment_hash` values at a configured rate
- **Compatibility**: Fully compatible. Fake reveals fail `verify_fulfillment` and are dropped. Existing `MAX_ABANDONS_PER_EPOCH` penalty must exempt dummy traffic (use a separate dummy identity or raise the abandon threshold)

### 3. Mixnet Routing

Fulfillment messages route through N relay nodes, each adding random delay.

- **Latency**: +N * avg_relay_delay (e.g., 3 hops * 2s = 6s typical, up to 15s tail)
- **Anonymity set**: All traffic flowing through the same relay set
- **Liveness**: Requires relay nodes to be online; relay failure breaks the path
- **Complexity**: Months. Requires onion-encrypted message format, relay discovery, path selection
- **Compatibility**: Orthogonal to commit-reveal. Can wrap existing messages without protocol changes, but needs new wire-layer infrastructure

### 4. Threshold Reveal (K-of-N Secret Sharing)

Split the fulfillment reveal across K parties using Shamir sharing. The fulfillment materializes only when K shares arrive, decorrelating timing from any single party.

- **Latency**: Bounded by the slowest of K parties (potentially unbounded in adversarial case)
- **Anonymity set**: K participants per fulfillment
- **Liveness**: Requires K of N to cooperate. If fewer than K respond, fulfillment stalls
- **Complexity**: Weeks. Shamir over BabyBear is trivial, but coordinating K reveals with timeout fallback is not
- **Compatibility**: Replaces the single-reveal step. The commit phase stays; the reveal becomes a multi-party aggregation

### 5. Batch Settlement (ZK Batch Proof)

Collect N fulfilled intents, generate a single recursive STARK proving all N were correctly fulfilled, submit one atomic turn settling all N simultaneously.

- **Latency**: Proportional to batch fill time (could be seconds or minutes depending on volume)
- **Anonymity set**: N (all intents in the batch)
- **Liveness**: Needs N intents to accumulate. Low-volume periods mean long waits or small batches
- **Complexity**: Weeks. The recursive STARK infrastructure exists (`recursive-proof-architecture.md`, `ivc.rs`), but batching N independent authorization proofs into one composite proof needs a new aggregation AIR
- **Compatibility**: Replaces `execute_fulfillment_flow` with a batch variant. Individual `create_fulfillment_turn` calls become batch entries

## Practical Path

**Implement now (existing architecture, no new infra):**

1. **Delay Pool** -- extend `FulfillmentRegistry` to hold reveals for a configurable batch interval before broadcasting. The existing `COMMIT_REVEAL_WINDOW_SECS` (5s) becomes the minimum commit window; add a `BATCH_RELEASE_INTERVAL_SECS` (30s) that gates when reveals are flushed. This is a ~200-line change to `commit_reveal_fulfillment.rs` plus a timer in the gossip loop.

2. **Dummy Traffic** -- add a background task generating fake commitments at a constant rate. Since `commitment_hash` is already opaque (BLAKE3), fakes are free. Cost is pure bandwidth: at 1 fake/s with 32-byte commitments, that is 2.7 KB/s per node.

Both can ship together. The delay pool ensures reveals are temporally batched; dummy traffic ensures commitments are indistinguishable from noise.

**Requires new infrastructure (later):**

- Mixnet routing (needs relay network, months of work)
- Batch settlement (needs aggregation AIR, weeks, but high payoff for on-chain cost reduction)
- Threshold reveal (niche; only worth it if the network grows adversarial relay sets)

**Key insight**: The existing 5-second commit window can be reframed as a *minimum hold* rather than a *target release*. Extend to 30s batch release with no protocol-breaking change -- fulfillers already tolerate up to `COMMITMENT_EXPIRY_SECS` (60s) of delay. The batch release sits well within that budget.

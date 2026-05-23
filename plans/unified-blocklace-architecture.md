# Unified Blocklace Architecture: Emergent Federations

## Executive Summary

This document proposes replacing the current "separate blocklace per federation" model with a single shared blocklace (the "fabric") where federations are emergent patterns -- groups of strands that mutually reference each other frequently enough to achieve finality. Cross-federation interaction becomes a first-class primitive: simply referencing another strand's block in the DAG.

The core insight: **tau already works this way**. It takes a participant set and ignores everything else. The only architectural change needed is removing the assumption that the Blocklace *container* is bounded to a fixed participant set. Everything else flows from that.

---

## 1. The Model

### Current Architecture

```
Federation A                    Federation B
┌─────────────┐                ┌─────────────┐
│ Blocklace_A │ ── CapTP ──── │ Blocklace_B │
│ {A1,A2,A3}  │   (TCP/TLS)   │ {B1,B2,B3}  │
│ tau({A1..}) │                │ tau({B1..}) │
└─────────────┘                └─────────────┘
```

- Each federation owns an isolated DAG
- Cross-federation = bilateral TCP sessions (CapTP)
- Participant set is defined by the Constitution *of that DAG*
- Dissemination only among federation members

### Proposed Architecture

```
                    The Fabric (one shared DAG)
┌──────────────────────────────────────────────────────────┐
│                                                          │
│   A1 ─── A2 ─── A3      (dense mutual references)       │
│    \      |      /         → tau({A1,A2,A3}) works       │
│     \     |     /                                        │
│      ╲    │    ╱                                         │
│       X ─ ─ ─ Y           (sparse cross-references)     │
│      ╱    │    ╲           → causal acknowledgment       │
│     /     |     \                                        │
│    /      |      \                                       │
│   B1 ─── B2 ─── B3      (dense mutual references)       │
│                            → tau({B1,B2,B3}) works       │
│                                                          │
│   C1 (sovereign strand, no group)                        │
│       → tau({C1}) = trivial self-finality                │
│                                                          │
└──────────────────────────────────────────────────────────┘
```

- ONE DAG, many strands
- "Federation" = the subset of strands running tau together
- Cross-federation = referencing another strand's block (causal link in the DAG)
- No CapTP required for causal acknowledgment (it becomes optional, for RPC semantics only)
- Sovereign nodes are just groups of size 1

### Key Definitions

| Term | Meaning |
|------|---------|
| **Strand** | A single participant's sequence of blocks (their "virtual chain") |
| **Reference group** | The set of strands that mutually reference each other within a wave |
| **Emergent federation** | A reference group dense enough to satisfy cordiality + super-ratification |
| **Cross-reference** | A block from strand A that includes a block from strand B (outside A's group) in its predecessors |
| **The fabric** | The single shared blocklace containing all strands |

---

## 2. How Tau Adapts

### The Critical Observation

Look at `tau_with_config` (ordering.rs:416-482):

```rust
pub fn tau_with_config(
    blocklace: &Blocklace,
    participants: &[[u8; 32]],
    config: &OrderingConfig,
) -> Vec<BlockId> {
    if participants.is_empty() || blocklace.blocks.is_empty() {
        return vec![];
    }
    let (rounds, max_round) = compute_rounds(blocklace);
    let final_leaders = find_all_final_leaders(blocklace, &rounds, max_round, participants, config);
    // ...
}
```

**Tau takes a participant list and a blocklace.** It computes rounds based on the DAG structure, then finds leaders among the given participants. It never assumes the blocklace contains ONLY those participants' blocks.

### Does Tau Still Produce Correct Ordering?

**Yes, with caveats.**

The round computation (`compute_rounds`) uses ALL blocks in the blocklace to determine depth via longest path. If the fabric contains blocks from strands D, E, F (not in our participant set), those blocks contribute to the round computation of blocks that reference them.

This is actually **correct behavior**: if A1 references a block from E, and that reference increases A1's computed round, then A1 genuinely happened "later" in causal time -- it saw E's block before producing its own. The round number reflects real causal depth.

**Potential issue: round inflation.** If strand A1 references blocks from 50 external strands, its computed round might jump far ahead of A2 and A3 (who only reference each other). This could cause A1's blocks to be in a different wave than A2/A3's blocks at the same "logical time," disrupting wave synchronization.

**Solution: Filtered round computation.** Compute rounds using ONLY blocks from the participant set:

```rust
/// Compute rounds considering only blocks from the given participants.
/// External blocks are treated as having round 0 (invisible).
fn compute_rounds_filtered(
    blocklace: &Blocklace,
    participants: &[[u8; 32]],
) -> (HashMap<BlockId, u64>, u64) {
    let participant_set: HashSet<[u8; 32]> = participants.iter().copied().collect();
    let mut rounds: HashMap<BlockId, u64> = HashMap::new();
    let mut max_round: u64 = 0;

    // Only process blocks from participants.
    let relevant_blocks: HashMap<&BlockId, &Block> = blocklace.blocks.iter()
        .filter(|(_, block)| participant_set.contains(&block.creator))
        .collect();

    // Topological sort of relevant blocks only.
    let mut in_degree: HashMap<BlockId, usize> = HashMap::new();
    let mut successors: HashMap<BlockId, Vec<BlockId>> = HashMap::new();

    for (&id, block) in &relevant_blocks {
        // Only count predecessors that are ALSO from participants.
        let pred_count = block.predecessors.iter()
            .filter(|p| relevant_blocks.contains_key(p))
            .count();
        in_degree.insert(*id, pred_count);
        for pred in &block.predecessors {
            if relevant_blocks.contains_key(pred) {
                successors.entry(*pred).or_default().push(*id);
            }
        }
    }

    // Kahn's algorithm (same as current, but restricted to participant blocks).
    let mut queue: VecDeque<BlockId> = in_degree.iter()
        .filter(|(_, deg)| **deg == 0)
        .map(|(id, _)| *id)
        .collect();

    while let Some(id) = queue.pop_front() {
        let block = &relevant_blocks[&id];
        let round = if block.predecessors.iter()
            .all(|p| !relevant_blocks.contains_key(p))
        {
            1  // No relevant predecessors = genesis round
        } else {
            1 + block.predecessors.iter()
                .filter_map(|p| rounds.get(p))
                .max()
                .copied()
                .unwrap_or(0)
        };
        rounds.insert(id, round);
        max_round = max_round.max(round);

        if let Some(succs) = successors.get(&id) {
            for &succ in succs {
                if let Some(deg) = in_degree.get_mut(&succ) {
                    *deg -= 1;
                    if *deg == 0 {
                        queue.push_back(succ);
                    }
                }
            }
        }
    }

    (rounds, max_round)
}
```

This preserves the existing tau semantics exactly: the participant group's rounds and waves are computed purely from their own inter-referencing pattern. External blocks are invisible to round computation but still exist in the DAG for causal ordering purposes.

### Can External Blocks Disrupt Tau?

With filtered round computation: **No.** The only way external blocks affect tau is through the `causal_past_inclusive` function used in `xsort`. When tau collects the "new blocks" for a finalized leader, it includes ALL blocks in the leader's causal past -- including external blocks.

This is a **feature, not a bug**: if the leader references an external block, that reference is part of the causal history that the group has agreed on. The external block gets ordered alongside the group's own blocks.

**Policy choice**: Should external blocks appear in tau's output?

- **Option A: Include them** (current `causal_past_inclusive` behavior). Any block in the causal past of a finalized leader gets ordered. Simple, sound, but means the group's total order includes foreign data.
- **Option B: Filter them** (only output blocks from participants). Cleaner separation of concerns -- the group only orders its own blocks. External references are still in the DAG but don't appear in the finalized turn stream.

**Recommendation: Option B** for the ordered output, with the external blocks still available as causal context. The modified `tau` function:

```rust
pub fn tau_unified(
    blocklace: &Blocklace,
    participants: &[[u8; 32]],
    config: &OrderingConfig,
) -> Vec<BlockId> {
    let participant_set: HashSet<[u8; 32]> = participants.iter().copied().collect();

    // Use filtered rounds (only participant blocks contribute to wave structure).
    let (rounds, max_round) = compute_rounds_filtered(blocklace, participants);
    let final_leaders = find_all_final_leaders(blocklace, &rounds, max_round, participants, config);

    let mut ordered = Vec::new();
    let mut prev_covered: HashSet<BlockId> = HashSet::new();

    for leader_id in &final_leaders {
        // Coverage and xsort as before, but filter output to participant blocks.
        let coverage = compute_leader_coverage(blocklace, &rounds, leader_id, participants, config);

        let new_blocks: HashSet<BlockId> = coverage.difference(&prev_covered)
            .copied()
            .filter(|bid| {
                if let Some(block) = blocklace.get(bid) {
                    // Only include blocks from participants (not external strands).
                    participant_set.contains(&block.creator)
                        && !has_equivocation_in_past(blocklace, &rounds, leader_id, &block.creator)
                } else {
                    false
                }
            })
            .collect();

        let sorted = xsort(blocklace, &new_blocks);
        ordered.extend(sorted);
        prev_covered = coverage;
    }

    ordered
}
```

---

## 3. Dissemination Changes

### Current Model

The `Disseminator` pushes ALL local blocks to ALL peers (within a federation). Peer knowledge tracking assumes a closed group.

### Unified Model: Interest-Based Dissemination

In the fabric, you don't push everything to everyone. You push to peers who **reference you** (your interest group):

```rust
/// A strand-aware disseminator for the unified blocklace.
///
/// Instead of pushing to all federation members, this pushes to peers
/// based on the referencing pattern (who references your blocks).
pub struct FabricDisseminator {
    /// The shared blocklace (local view).
    blocklace: Blocklace,
    /// Our identity.
    self_key: NodeKey,
    /// Peers we actively disseminate to (our "subscribers").
    /// These are strands that reference our blocks.
    subscribers: HashSet<NodeKey>,
    /// Peers we want blocks from (our "subscriptions").
    /// These are strands whose blocks we reference.
    subscriptions: HashSet<NodeKey>,
    /// Per-peer knowledge estimates (same as current PeerKnowledge).
    peer_knowledge: PeerKnowledge,
    /// Pending blocks waiting for predecessors.
    pending: HashMap<BlockId, (Block, HashSet<BlockId>)>,
}

impl FabricDisseminator {
    /// Determine what to push to a subscriber.
    ///
    /// We only send blocks from strands that the subscriber is interested in.
    /// Specifically: we send our own blocks, plus blocks from strands that
    /// both we and the subscriber reference (shared reference group).
    pub fn blocks_to_send(&self, peer: &NodeKey, peer_interests: &HashSet<NodeKey>) -> DeltaGroup {
        let peer_known = self.peer_knowledge.known_by(peer)
            .cloned()
            .unwrap_or_default();

        // Blocks to send: our own blocks + blocks from shared interests
        // that the peer doesn't have.
        let relevant_creators: HashSet<NodeKey> = self.subscriptions
            .intersection(peer_interests)
            .copied()
            .chain(std::iter::once(self.self_key))
            .collect();

        let relevant_unknown: HashSet<BlockId> = self.blocklace.block_ids()
            .into_iter()
            .filter(|id| {
                !peer_known.contains(id) &&
                self.blocklace.get(id)
                    .map(|b| relevant_creators.contains(&b.creator))
                    .unwrap_or(false)
            })
            .collect();

        // Build causally-closed delta from relevant_unknown.
        self.build_causal_delta(&relevant_unknown, &peer_known)
    }

    /// Discovery: when we see a block referencing an unknown strand,
    /// we can choose to subscribe to that strand.
    pub fn discover_strand(&mut self, new_strand: NodeKey) {
        // Add to subscriptions if we're interested.
        // Interest policy is application-level (e.g., same cell group, same executor).
        self.subscriptions.insert(new_strand);
    }

    /// When another strand starts referencing us, they become a subscriber.
    pub fn add_subscriber(&mut self, subscriber: NodeKey) {
        self.subscribers.insert(subscriber);
    }
}
```

### Gossip Topology

The gossip topology matches the referencing pattern:

```
If A references B → A subscribes to B → B pushes to A
If B references A → B subscribes to A → A pushes to B
If both reference each other → bidirectional push (federation behavior)
```

This means:
- **Within a federation**: full bidirectional push (same as current behavior)
- **Cross-federation**: unidirectional or sparse push (only when referenced)
- **Sovereign strands**: only push to peers that subscribe to you

### Selective Sync (Causal Closure Without Full History)

A node in the fabric does NOT need the entire DAG. It needs:

1. All blocks from its reference group (for tau to work)
2. The causal closure of those blocks (so predecessors can be verified)
3. NOT blocks from distant strands (unless they're in the causal past of a reference group block)

This naturally bounds sync cost. A group of size n only syncs n strands' worth of blocks, plus the minimal causal context from external references.

```rust
/// Compute the minimal set of blocks needed for a reference group to run tau.
pub fn minimal_sync_set(
    blocklace: &Blocklace,
    reference_group: &[[u8; 32]],
) -> HashSet<BlockId> {
    let group_set: HashSet<[u8; 32]> = reference_group.iter().copied().collect();
    let mut needed = HashSet::new();

    // All blocks from group members.
    for (id, block) in &blocklace.blocks {
        if group_set.contains(&block.creator) {
            needed.insert(*id);
            // Plus the causal closure of each group block.
            let past = blocklace.causal_past(id);
            needed.extend(past);
        }
    }

    needed
}
```

---

## 4. Executor Roles in the Unified Model

### The Spectrum

In the unified model, execution strategy is a per-strand choice:

| Mode | Who executes | Who proves | Trust | Use case |
|------|-------------|-----------|-------|----------|
| **Sovereign** | Self | Self | Minimal (verify own proofs) | Privacy-maximizing, phones with proving |
| **Delegated** | Executor strand | Executor strand | Trust executor for liveness + censorship-resistance | Phone users, batch efficiency |
| **Replicated** | All group members | All (verify each other) | Maximum (BFT, no single point of failure) | High-value assets, shared state |

### Executor as a Strand

An executor is not a special node -- it's just a strand that other strands trust:

```rust
/// An executor's block contains state transitions for multiple clients.
///
/// The executor strand produces blocks with `BatchExecution` payloads that
/// include proof of correct execution for each client turn.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BatchExecution {
    /// Client turns included in this batch (ordered).
    pub turns: Vec<ClientTurn>,
    /// STARK proof covering all turns in the batch.
    pub batch_proof: Vec<u8>,
    /// Post-state commitment after all turns.
    pub post_state_root: [u8; 32],
}

/// A client's turn as included in an executor's batch.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ClientTurn {
    /// The client strand's public key.
    pub client: NodeKey,
    /// The block from the client strand requesting this turn.
    pub request_block: BlockId,
    /// The turn data (effects).
    pub turn_data: Vec<u8>,
    /// Post-execution state commitment for this client's cell.
    pub post_state: [u8; 32],
}
```

### Trust = Referencing

A client trusts an executor by referencing the executor's output blocks:

```
Client C's block at seq 5:
  predecessors: [C_seq4, Executor_batch_17]
  payload: Ack (acknowledging Executor_batch_17 as authoritative for C's state)
```

The executor knows C trusts them because C references their blocks. If C stops referencing them, C has effectively "fired" the executor (delegated elsewhere or gone sovereign).

### Executor Rotation and Challenge

```rust
/// A client can challenge an executor's output by producing a conflicting
/// state transition proof. This is visible in the DAG because:
/// 1. The executor published batch_proof with post_state X for client C.
/// 2. Client C publishes a block with their own proof showing post_state Y.
/// 3. Other strands can verify both proofs and determine who is correct.
///
/// The reference group (the "federation" the executor belongs to) can then
/// evict the cheating executor via the standard constitution mechanism.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum ExecutorChallenge {
    /// Client claims executor computed wrong post-state.
    IncorrectExecution {
        batch_block: BlockId,
        client: NodeKey,
        claimed_post_state: [u8; 32],
        correct_post_state: [u8; 32],
        proof: Vec<u8>,
    },
    /// Client claims executor censored their turn (turn was submitted N waves ago).
    Censorship {
        request_block: BlockId,
        submitted_at_wave: u64,
        current_wave: u64,
    },
}
```

---

## 5. Constitution Becomes a Lens

### Current: Constitution Owns a Blocklace

```rust
// Current: constitution is tightly coupled to a specific blocklace
pub struct ConstitutionManager {
    pub current: Constitution,  // participants of THIS federation
    // ...
}
```

### Proposed: Constitution is a View Over the Fabric

```rust
/// A ReferenceGroup is a "lens" over the unified blocklace.
/// It defines which strands form a consensus group and runs tau over them.
///
/// Multiple ReferenceGroups can coexist over the same underlying fabric --
/// they just look at different strand subsets.
pub struct ReferenceGroup {
    /// The strands in this group (equivalent to current `Constitution.participants`).
    pub members: Vec<NodeKey>,
    /// Supermajority threshold for this group.
    pub threshold: usize,
    /// Timeout for inactivity-based removal.
    pub timeout_waves: u64,
    /// The ordering config for this group's tau.
    pub ordering_config: OrderingConfig,
    /// Version (incremented on membership change).
    pub version: u64,
}

impl ReferenceGroup {
    /// Run tau over the fabric, considering only this group's strands.
    pub fn finalize(&self, fabric: &Blocklace) -> Vec<BlockId> {
        tau_unified(fabric, &self.members, &self.ordering_config)
    }

    /// Check if a new strand should be added to this group.
    ///
    /// In the emergent model, a strand "joins" by referencing group members.
    /// The group detects this and can auto-admit (or require a vote).
    pub fn detect_join_candidate(&self, fabric: &Blocklace) -> Vec<NodeKey> {
        let member_set: HashSet<NodeKey> = self.members.iter().copied().collect();
        let mut candidates: HashMap<NodeKey, usize> = HashMap::new();

        // Find non-member strands that reference group members.
        for (_, block) in &fabric.blocks {
            if member_set.contains(&block.creator) {
                continue;
            }
            // Count how many group members this outsider references.
            let refs_to_group = block.predecessors.iter()
                .filter(|p| fabric.get(p).map(|b| member_set.contains(&b.creator)).unwrap_or(false))
                .count();
            if refs_to_group > 0 {
                *candidates.entry(block.creator).or_insert(0) += refs_to_group;
            }
        }

        // A strand that references the majority of group members frequently
        // is a join candidate.
        let reference_threshold = self.members.len() / 2;
        candidates.into_iter()
            .filter(|(_, count)| *count > reference_threshold)
            .map(|(key, _)| key)
            .collect()
    }

    /// Detect strands that have stopped referencing group members.
    /// These are candidates for removal (natural departure).
    pub fn detect_departure(&self, fabric: &Blocklace, current_wave: u64) -> Vec<NodeKey> {
        // Same logic as current timeout detection, but based on
        // referencing pattern rather than block production.
        // A strand that produces blocks but stops referencing the group
        // is departing (even if still active elsewhere).
        vec![] // placeholder
    }
}
```

### The Emergent Federation Lifecycle

```
1. GENESIS: Alice creates her first block. She is a sovereign strand.
   Group: {Alice}, threshold: 1, tau trivially finalizes everything.

2. PAIR: Bob starts referencing Alice's blocks. Alice references Bob's.
   Group: {Alice, Bob}, threshold: 2.
   tau now requires both to produce blocks for finality.

3. GROWTH: Carol references both Alice and Bob. They reference Carol.
   Group: {Alice, Bob, Carol}, threshold: 3.
   tau({A,B,C}) produces ordering.

4. CONSTITUTION: The group records in their blocks: "we agree on 2/3 threshold."
   This is just a payload convention -- a block saying "I consider {A,B,C} my group."
   Not enforced by the fabric, enforced by group members refusing to reference
   blocks from equivocators or non-members.

5. DEPARTURE: Dave stops referencing the group.
   After timeout_waves, his round stops advancing. tau stops including him.
   Group: {Alice, Bob, Carol} again (naturally).

6. NO GOVERNANCE VOTE NEEDED: Join = start referencing. Leave = stop referencing.
   The constitution records the current state, but the referencing pattern IS the truth.
```

---

## 6. Privacy in a Shared Lace

### What Is Visible

| To whom | What they see |
|---------|--------------|
| Your reference group | Your blocks, your activity pattern, your payload commitments |
| Distant strands | Nothing (unless someone bridges) |
| Anyone with a block | That block's existence + predecessors (causal structure) |
| Executor (if delegated) | Your full state (necessary for execution) |

### What Is Hidden

- **Block content**: Encrypted payloads (sovereign cells). Only the commitment is visible in the DAG.
- **Activity to distant strands**: They don't receive your blocks unless subscribed.
- **Which group you're in**: Your predecessor set reveals who you reference, but outsiders don't see your blocks unless they're subscribed.

### The Bridge Problem

If Alice (group {A,B,C}) references Eve's block (group {D,E,F}), then:
- Alice's group now has Eve's block in their causal history
- Eve's group does NOT necessarily have Alice's block (unless Eve references Alice back)
- This is unidirectional causal acknowledgment -- Alice proved she saw Eve's block

This is fine for privacy: Alice chose to reveal her awareness of Eve. Eve didn't reveal anything to Alice's group beyond the one referenced block.

### Selective Disclosure

```rust
/// A cross-group reference can include a proof without revealing the full block content.
/// The reference says "I saw block X from strand E" and includes just the commitment,
/// not the decrypted payload.
pub struct CrossReference {
    /// The referenced block's ID (hash commitment).
    pub block_id: BlockId,
    /// The referenced block's creator.
    pub creator: NodeKey,
    /// Optional: a ZK proof about the referenced block's content
    /// (e.g., "this block contains a valid transfer to me").
    pub proof: Option<Vec<u8>>,
}
```

---

## 7. Scalability Analysis

### Is O(n) Predecessor Vectors Worse in a Shared Lace?

**No -- it stays the same within a group.** The cordiality requirement is per-group: each block must reference >2n/3 blocks from the previous round *of its reference group*. In the unified model, n is the size of YOUR group, not the size of the entire fabric.

A block's predecessor vector contains:
1. References to the previous round's group members (~n entries, same as current)
2. Optional cross-references to external strands (0 to a few entries)

The cross-references are OPTIONAL and sparse. They don't contribute to cordiality. They're just causal links for cross-group interaction.

### Fabric-Wide Scalability

| Metric | Separate laces | Unified fabric |
|--------|---------------|----------------|
| Blocks stored per node | Only own federation's | Own group + causal closure |
| Predecessor vector size | O(n) where n = federation size | O(n) where n = group size + O(k) cross-refs |
| Dissemination per round | Push to n-1 peers | Push to subscribers (interest-based) |
| tau cost | O(n * blocks_in_lace) | O(n * blocks_from_group) (filtered) |
| Storage growth | O(n * blocks/wave) | O(n * blocks/wave) + O(cross-refs) |

The unified model does NOT make anything worse within a group. The only additional cost is storing and transmitting the occasional cross-reference block from an external strand.

### What About a Fabric with 10,000 Strands?

You don't store 10,000 strands' blocks. You only store:
- Your group's blocks (e.g., 10 strands)
- Causal closure of blocks you've referenced (a few external blocks per cross-ref)
- Blocks pushed to you by subscribers (only those relevant to your interests)

A node in a 10-strand group within a 10,000-strand fabric stores approximately the same amount as a node in a 10-node isolated federation today.

### The Real Scalability Win

The unified model eliminates the overhead of CapTP sessions for simple cross-group interactions:

| Operation | Current (CapTP) | Unified (DAG reference) |
|-----------|----------------|------------------------|
| Acknowledge foreign block | TCP session + handshake + message | One predecessor hash in your next block |
| Cross-federation proof delivery | TCP + serialize + deserialize | Block payload in DAG (naturally propagated) |
| Establish trust relationship | Sturdy ref + 3-party handoff | Start referencing their blocks |
| Discover new peers | Out-of-band directory | See them in blocks from people you follow |

---

## 8. Concrete Migration Path

### Phase 1: Generalize the Blocklace Container (Low Risk)

The `Blocklace` struct already stores blocks from any creator. The only assumption of a fixed participant set is in `tau` and `Constitution`. We change nothing in the container.

**Changes:**
- Add `compute_rounds_filtered` as an alternative round computation
- Add `tau_unified` that uses filtered rounds and filters output to participant blocks
- Existing tests pass unchanged (unified tau produces same output for isolated groups)

```rust
// In ordering.rs: add alongside existing functions (non-breaking)

pub fn tau_unified(
    blocklace: &Blocklace,
    participants: &[[u8; 32]],
    config: &OrderingConfig,
) -> Vec<BlockId> {
    // ... (as sketched above)
}
```

### Phase 2: Interest-Based Dissemination (Medium Risk)

Replace the "push to all" model with subscription-based push.

**Changes:**
- Add `FabricDisseminator` alongside existing `Disseminator`
- New disseminator respects subscription/subscriber lists
- Existing `Disseminator` continues to work (a federation that subscribes to all its members = current behavior)

The key insight: a traditional federation is just a `FabricDisseminator` where every member subscribes to every other member. The new model is a strict generalization.

### Phase 3: ReferenceGroup Replaces Constitution for Membership (Medium Risk)

**Changes:**
- `ReferenceGroup` struct with same fields as `Constitution` + ordering config
- `ReferenceGroup::finalize()` calls `tau_unified`
- `ConstitutionManager` delegates to a `ReferenceGroup` internally
- New API: `detect_join_candidate`, `detect_departure` based on referencing patterns
- Existing `Constitution` API continues to work (wrapped around `ReferenceGroup`)

### Phase 4: Cross-Group References as First-Class (Low Risk)

**Changes:**
- Allow blocks to have predecessors from non-member strands (already works -- no code change)
- Add discovery: when a member references an external block, group members receive it as causal context
- Add `CrossReference` metadata for blocks that reference external strands
- CapTP becomes optional: still used for RPC semantics (invoke/deliver), but simple acknowledgment and proof exchange happen via the DAG

### Phase 5: Executor Delegation (New Feature)

**Changes:**
- `BatchExecution` payload type
- Client-executor protocol: client submits turn request block, executor includes it in batch
- Challenge mechanism: client can dispute executor output by publishing conflicting proof
- Executor rotation: client changes which executor they reference

### Phase 6: Remove Federation Boundary Assumption (Final)

**Changes:**
- Wire protocol no longer requires `FederationId` for routing (replaced by strand-based addressing)
- Checkpoint proofs are per-group (not per-federation)
- State migrations become group-to-group (same DAG, just change which strands you reference)

---

## 9. What Stays the Same

| Component | Changes? | Why |
|-----------|---------|-----|
| Block structure | No | Blocks already support arbitrary predecessors |
| Block ID computation | No | Hash of content, independent of group membership |
| tau correctness proof | No | tau over a subset of a larger DAG = tau over a smaller DAG (with filtered rounds) |
| Effect VM | No | Proves state transitions regardless of DAG topology |
| STARK/Plonky3 prover | No | Operates on traces, doesn't know about DAG |
| Capability model | No | Caps are per-cell, orthogonal to DAG structure |
| IVC folding | No | Accumulates proofs regardless of source |
| Equivocation detection | No | Same creator + same seq + different content |
| Cordiality check | Minor | Uses filtered participant set (same logic) |

---

## 10. Risks and Mitigations

### Risk: Sybil Amplification

In an open fabric, anyone can create strands. A Sybil attacker creates 1000 strands and references your group, hoping to be auto-admitted.

**Mitigation**: Join requires group consent (vote), not just referencing. The referencing pattern is a SIGNAL, not an automatic admission mechanism. The constitution's voting requirement remains.

### Risk: DAG Pollution

External strands produce blocks that end up in your causal past (because one of your members referenced them). Your storage grows.

**Mitigation**: 
- Causal closure only adds blocks transitively reachable from blocks you care about
- Cross-references are opt-in (a member choosing to reference an external block is choosing to include it in the group's causal context)
- Groups can enforce policy: "don't reference external blocks without group approval" (enforced by refusing to ratify blocks with unauthorized external references)

### Risk: Round Inflation (Without Filtered Rounds)

If a member references a deep external chain, their computed round jumps ahead.

**Mitigation**: Filtered round computation (Phase 1). Rounds are computed only over participant blocks. External references don't inflate rounds.

### Risk: Increased Complexity for Light Clients

Light clients currently only need one federation's checkpoint. In the unified model, a checkpoint covers a group -- but the group's causal history might include external blocks.

**Mitigation**: Checkpoint proofs cover only the group's state (same as today). External blocks in the causal past are included in the checkpoint proof's causal closure but don't affect the state commitment (they're just ordering context).

### Risk: CapTP Becomes Redundant

If cross-group interaction can happen via DAG references, does CapTP still have a purpose?

**Answer: Yes.** DAG references provide causal acknowledgment (I saw your block). CapTP provides RPC semantics (invoke a method on a remote object, get a response). These are complementary:
- **DAG reference**: "I acknowledge this event happened" (pub/sub, consensus voting, proof delivery)
- **CapTP invoke**: "Execute this action and return a result" (interactive protocols, stateful sessions)

The unified model reduces the NEED for CapTP (many operations become DAG-native) but doesn't eliminate its value for interactive patterns.

---

## 11. Summary

The unified blocklace is not a rewrite. It is recognizing what the code already nearly supports:

1. **tau already works on subsets** -- just needs filtered round computation to be DAG-topology-independent
2. **Blocklace already stores any creator's blocks** -- no assumption of bounded membership at the data layer
3. **Dissemination already uses interest-based delta computation** -- just needs explicit subscription management instead of implicit "everyone in my federation"
4. **Constitution already manages membership independently of the DAG** -- just needs to become a "view" rather than an "owner"

The migration is incremental, backward-compatible at each phase, and each phase independently delivers value:
- Phase 1 enables running tau over shared DAGs (testing, simulation)
- Phase 2 reduces network overhead (only push what's needed)
- Phase 3 enables emergent federation formation (no upfront coordination needed)
- Phase 4 eliminates CapTP overhead for simple cross-group interactions
- Phase 5 enables efficient batched execution (amortized proving)
- Phase 6 completes the vision: one fabric, emergent groups, sovereign by default

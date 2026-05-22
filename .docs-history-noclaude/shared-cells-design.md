# Shared Cells and Multi-Owner Authorization: Design Exploration

## Problem Statement

Pyana cells currently have a single `public_key: [u8; 32]` owner. The executor verifies
Ed25519 signatures against this key. This model supports single-agent autonomy but
cannot directly express:

- **Joint accounts**: M-of-N authorization (e.g., 2-of-3 multisig)
- **Shared resources**: Multiple agents read/write a common cell
- **Escrow**: Cell locked until conditions met by multiple independent parties
- **DAOs/committees**: Threshold decision-making over shared state

This document explores the design space and recommends an approach that preserves
pyana's fast-path properties while enabling multi-owner patterns.

---

## Current Architecture Summary

### Cell Ownership (cell/src/cell.rs)

```rust
pub struct Cell {
    pub id: CellId,                          // BLAKE3(public_key || token_id)
    pub public_key: [u8; 32],                // Single Ed25519 owner
    pub state: CellState,                    // 8 fields + nonce + balance
    pub permissions: Permissions,            // Per-action auth requirements
    pub verification_key: Option<VerificationKey>,  // ZK proof validation
    pub capabilities: CapabilitySet,         // C-list: reachable cells
    pub program: CellProgram,               // State transition constraints
    ...
}
```

### Authorization Model (cell/src/permissions.rs)

Each action type requires one of: `None`, `Signature`, `Proof`, `Either`, `Impossible`.
Signature verification checks against the cell's single `public_key`.

### Capability Delegation (cell/src/capability.rs, cell/src/delegation.rs)

Cells hold capability references (c-list entries) that grant access to other cells.
Capabilities can be attenuated (narrowed) and delegated. The `DelegatedRef` mechanism
provides snapshot+refresh E-style delegation from parent to child.

### Fast Path (turn/src/conflict.rs)

Conflict detection uses Bloom filters over read/write access sets. Two turns with
non-overlapping conflict sets can be parallelized without consensus. This is directly
analogous to Sui's owned-object fast path.

### Multi-Party Composition (turn/src/composer.rs)

`CommitmentMode::Partial` already enables independent parties to sign their own
actions, which a composer assembles into a single atomic Turn. This provides
composability (DEX fills, atomic swaps) without shared ownership.

---

## How Sui Handles It (Lutris Paper Analysis)

Sui distinguishes three object types:

| Sui Object Type | Consensus Path | Authorization | Latency |
|---|---|---|---|
| **Owned** | Fast path (broadcast only) | Single signer | ~480ms |
| **Read-only/Immutable** | Fast path | None needed | ~480ms |
| **Shared** | Full consensus (Bullshark) | Contract logic | ~3s |

Key insights from the Sui paper:

1. **Owned objects use Byzantine consistent broadcast** (no consensus needed). Safety
   comes from ObjKey locking: a validator signs at most one transaction per
   (ObjID, Version).

2. **Shared objects ALWAYS go through consensus**. There is no fast path for shared
   objects. The paper states: "Such objects, by virtue of having to support multiple
   writers while ensuring safety and liveness, require a full agreement protocol."

3. **No multi-sig at the object level**. Sui uses a single authorization path per
   owned object. Multi-sig is handled at the address/wallet layer (a multi-sig
   address can own objects), not at the object type level.

4. **Objects can be "child objects"** owned by other objects. The parent must be
   present in the transaction to access the child. This enables composable data
   structures without making them shared.

### Mapping to Pyana

| Sui Concept | Pyana Equivalent | Notes |
|---|---|---|
| Owned object | Cell with single `public_key` | Current model |
| Shared object | ? | **This design doc** |
| Immutable object | Cell with `Permissions::frozen()` | Already supported |
| Child object | Cell with `delegate: Some(parent_id)` | Partially implemented |
| ObjKey lock | Nonce replay protection | Similar anti-equivocation |
| Multi-sig address | ? | Not yet in pyana |

---

## Design Options

### Option A: Multi-Key Cell (`owners: Vec<PublicKey>` + threshold)

Add a threshold signature scheme directly to the Cell struct:

```rust
pub struct Cell {
    pub auth_keys: Vec<[u8; 32]>,  // N authorized keys
    pub threshold: u8,              // K-of-N required
    // ... rest unchanged
}
```

**Pros:**
- Simple mental model
- Direct multi-sig without wrapping

**Cons:**
- **Breaks CellId derivation**: Currently `CellId = BLAKE3(public_key || token_id)`.
  Multiple keys means the identity depends on the key set, making key rotation
  complex (rotating one key changes the cell's identity).
- **Breaks fast path**: With multiple owners, the executor cannot verify a turn
  touches only one signer's cells. Two owners could submit conflicting turns for
  the same cell, requiring consensus to resolve (exactly Sui's shared-object problem).
- **Verification cost**: Must verify K signatures per action instead of 1.
- **Key management complexity**: Adding/removing owners requires coordinated
  state change.

### Option B: Auth Policy Enum

Replace the single key with a flexible authorization policy:

```rust
pub enum AuthPolicy {
    Single(PublicKey),
    Threshold { keys: Vec<PublicKey>, k: u8 },
    Script(PredicateHash),  // Custom authorization predicate (ZK circuit)
    Timelock { key: PublicKey, release_height: u64 },
}

pub struct Cell {
    pub id: CellId,
    pub auth_policy: AuthPolicy,
    // ...
}
```

**Pros:**
- Maximum flexibility
- Covers multi-sig, timelocks, and custom scripts
- `Script` variant enables arbitrary authorization logic via ZK proofs

**Cons:**
- **Same CellId problem as Option A** for non-Single variants
- **Same fast-path problem**: Threshold cells need consensus
- **Complexity tax**: Every code path that checks authorization must handle all
  variants
- **Migration cost**: Existing cells must be migrated or wrapped
- **Partial-order issues**: The existing `AuthRequired` lattice
  (`None < Signature/Proof < Either < Impossible`) becomes much more complex
  with custom predicates

### Option C: Keep Cells Single-Owner, Model Shared State via Capabilities (Recommended)

**Core insight**: Pyana already has the building blocks for multi-owner semantics
via the capability system. Rather than changing the Cell ownership model, we
introduce a new cell archetype: the **governed cell**.

A governed cell:
- Has `public_key = [0u8; 32]` (the "nobody" key -- no single signer)
- Uses `AuthRequired::Proof` for all actions
- Carries a `CellProgram::Circuit` that encodes the authorization policy
- Is accessed via capabilities held by authorized parties

```rust
// No new types needed! Just a pattern using existing primitives:
let governed = Cell {
    public_key: GOVERNANCE_SENTINEL,  // e.g., all-zeros
    permissions: Permissions {
        send: AuthRequired::Proof,
        set_state: AuthRequired::Proof,
        // ...
    },
    program: CellProgram::Circuit {
        circuit_hash: governance_circuit_hash,
    },
    verification_key: Some(governance_vk),
    capabilities: CapabilitySet::new(),
    // ...
};
```

The governance circuit proves: "K of these N authorized public keys signed
this state transition." The proof itself is a ZK proof of a multi-sig, meaning
the verifier (executor) sees only: "the governance policy was satisfied" -- not
which specific parties signed.

**Pros:**
- **No structural changes** to Cell, CellId, or the executor
- **Fast path preserved** for cells that aren't governed (vast majority)
- **Privacy**: Ring signatures / anonymous credentials fall naturally out of ZK
  proof authorization -- prove "I'm one of the N" without revealing which one
- **Composable with existing features**: capabilities, delegation, conditional
  turns, and the composer all work unchanged
- **Flexible policies**: The circuit can encode any policy (threshold, weighted
  voting, time-delayed, conditional on external state)
- **No consensus requirement for governance updates**: Changing the authorized set
  means updating the verification key (governed by the old key set via proof)
- **Escrow is trivial**: Governed cell with a circuit that requires proofs from
  both parties (or a timeout condition via ConditionalTurn)

**Cons:**
- **Proof overhead**: Every action on a governed cell requires generating a ZK
  proof (this is the "consensus cost" -- computation replaces communication)
- **Requires circuit infrastructure**: Must build governance circuits
  (threshold-sig verification in STARK/R1CS)
- **Learning curve**: Users must understand that "shared state = governed cell
  with proof auth" rather than a simple multi-sig field
- **Still needs consensus for concurrent access**: Two parties submitting
  conflicting proofs to the same governed cell at the same time is an
  equivocation -- requires ordering

---

## Recommended Approach: Option C with Consensus Annotation

The recommended design is Option C (governed cells via proof authorization) with
one structural addition: a **consensus annotation** on cells that require ordering.

### New Field: `access_mode`

```rust
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum AccessMode {
    /// Single-owner fast path. Only the owner can submit turns touching this cell.
    /// Equivocation by the owner locks the cell until epoch boundary (Sui-style).
    Owned,

    /// Shared: multiple writers possible. Turns touching this cell MUST go through
    /// consensus ordering. The federation's conflict detector treats this cell as
    /// always-conflicting with other turns that also touch it.
    Shared,

    /// Immutable: no writes allowed (frozen). Can be used by any turn without
    /// consensus (read-only fast path).
    Immutable,
}
```

```rust
pub struct Cell {
    pub id: CellId,
    pub public_key: [u8; 32],
    pub access_mode: AccessMode,  // NEW
    // ... rest unchanged
}
```

### Interaction with Fast Path

The fast path logic in `conflict.rs` already computes read/write access sets.
The federation node can use `access_mode` to route turns:

- **Turn touches only `Owned` cells belonging to the turn's agent**: Fast path
  (Byzantine consistent broadcast, no consensus needed)
- **Turn touches any `Shared` cell**: Must go through consensus ordering
- **Turn only reads `Immutable` cells**: Fast path (no conflict possible)

This mirrors Sui's routing exactly:

```
if turn.write_set.iter().all(|cell| cell.access_mode == Owned && cell.owner == turn.agent) {
    fast_path(turn)  // ~480ms equivalent
} else {
    consensus_path(turn)  // ordered by federation consensus
}
```

### Governed Cell Pattern (for Multi-Owner)

For M-of-N authorization over a shared cell:

1. **Create cell** with `access_mode: Shared` and `permissions: zkapp()` (proof-required)
2. **Deploy governance circuit** that verifies K-of-N signatures inside ZK
3. **Set verification key** to the governance circuit's VK
4. **Grant capabilities** to each authorized party's cell, pointing at the governed cell
5. **Access**: Each party constructs their partial signature, K of them collaborate
   to produce the ZK proof, and one submits the turn

### Example: 2-of-3 Multi-Sig Treasury

```
Treasury Cell:
  access_mode: Shared
  public_key: [0; 32]  (sentinel: no single signer)
  permissions: Permissions::zkapp()  (all actions require proof)
  verification_key: Some(threshold_2_of_3_vk)
  program: Circuit { circuit_hash: threshold_circuit }

Alice's Cell → holds CapabilityRef { target: treasury, permissions: Either }
Bob's Cell   → holds CapabilityRef { target: treasury, permissions: Either }
Carol's Cell → holds CapabilityRef { target: treasury, permissions: Either }
```

To spend from treasury, any 2 of {Alice, Bob, Carol} provide signatures.
One of them generates a ZK proof: "2 of these 3 keys signed this action."
The proof is submitted as `Authorization::Proof` on the turn.

---

## Interaction with ZK Proofs and Privacy

### Anonymous Authorization

The ZK proof approach naturally enables anonymous credentials:

- **Ring signature simulation**: Prove "I hold one of these N keys and I signed
  this message" without revealing which key. The `Authorization::Proof` variant
  already supports this -- the verifier checks the proof against the governance
  circuit's VK without learning which party produced it.

- **Weighted voting**: The circuit can encode different weights per key. Prove
  "the sum of weights of signers >= threshold" without revealing the signer set.

- **Credential delegation**: A DAO member can delegate their voting power to
  another key by providing a proof that chains: "this new key was authorized by
  a key in the authorized set."

### Privacy Properties

| Property | Achieved? | How |
|---|---|---|
| Hide which K-of-N signed | Yes | ZK proof over signature set |
| Hide N (total authorized set size) | Partial | Fixed-size circuit can pad |
| Hide that it's multi-owner at all | Yes | From outside, looks like any proof-auth cell |
| Forward secrecy of past votes | Yes | Proofs are zero-knowledge |

---

## Interaction with Existing Subsystems

### Capabilities and Delegation

No changes needed. Capabilities already model "Cell A can access Cell B with
permissions P." The governed cell pattern uses this directly:

- Each authorized party holds a capability to the governed cell
- The capability's `permissions` field can attenuate access (e.g., read-only
  members get `AuthRequired::None` for reads, but the cell's own permissions
  still require proof for writes)
- Revocation works: revoke a party's capability to remove their access

### Conditional Turns

Conditional turns compose naturally with governed cells:

- "This treasury withdrawal executes IFF a proof from the governance circuit
  arrives before height H" = time-locked multi-sig
- Cross-federation escrow: governed cell on Fed A, conditional on receipt from Fed B

### Turn Composer

`CommitmentMode::Partial` already handles the "multiple parties contribute to one
turn" case. For governed cells, composition works at two levels:

1. **Multiple turns touching the same shared cell**: Routed through consensus
   (the `Shared` access mode ensures ordering)
2. **One turn with multiple signers**: Composer assembles partial-commitment
   actions; the governance proof covers the multi-party authorization

### Conflict Detection

The existing Bloom filter approach needs one refinement:

```rust
pub fn extract_access_sets(turn: &Turn) -> (Vec<CellId>, Vec<CellId>) {
    // ... existing logic ...
    // NEW: if any cell in the write set has access_mode == Shared,
    // the federation routes this turn through consensus.
}
```

The `ConflictSet` Bloom filter still works for detecting potential parallelism
among consensus-path turns (Bullshark commit batching / Block-STM style parallel
execution within a batch).

### Fee Distribution and Budget Gate

No changes. Governed cells pay fees like any other cell. The budget gate
(Stingray bounded counter) operates at the silo level, independent of cell
ownership model.

### Note System and Bridges

Notes are already cell-independent (they use nullifiers and commitments).
A governed cell can hold balance and transact notes normally. The bridge
system (BridgeLock/BridgeMint/BridgeFinalize) operates on note values, not
cell ownership -- no interaction.

---

## Comparison with seL4/Robigalia Capability Model

seL4's capability system has relevant parallels:

| seL4 Concept | Pyana Equivalent | Shared-Cell Relevance |
|---|---|---|
| Endpoint (IPC channel) | Cell with `access_mode: Shared` | Multiple processes invoke |
| CNode (capability space) | `CapabilitySet` (c-list) | Each party holds caps |
| Badge (sender ID in msg) | `breadstuff` token hash | Identify which party acted |
| Mint/Revoke | `grant`/`revoke` on CapabilitySet | Dynamic membership |
| Reply capability (one-shot) | `expires_at` on CapabilityRef | Time-bounded access |

Key lesson from seL4: **shared endpoints don't need shared ownership**.
Multiple processes can invoke the same endpoint because they each hold a
capability TO it. The endpoint itself has a single "owner" (the server
process). Authorization is capability-based, not identity-based.

This validates Option C: pyana cells are endpoints. Multiple agents can
invoke a governed cell because they hold capabilities to it. The cell's
program (circuit) defines what operations are valid, not who "owns" it.

---

## Migration Path

### Phase 1: Access Mode Annotation (Structural, No Behavioral Change)

Add `access_mode: AccessMode` to `Cell` with default `Owned`. This is
backward-compatible: all existing cells get `access_mode: Owned` and behavior
is unchanged. The executor does not yet enforce routing -- this is metadata
for the federation's turn router.

```rust
// cell/src/cell.rs
pub struct Cell {
    pub access_mode: AccessMode,  // default: Owned
    // ... existing fields
}
```

### Phase 2: Federation Routing

The node layer (`node/src/`) uses `access_mode` to route incoming turns:
- `Owned` cells: fast path (current behavior)
- `Shared` cells: consensus path (federation orders turns before execution)

This requires the federation to:
1. Inspect the turn's write set
2. Check each written cell's `access_mode`
3. Route accordingly

No executor changes needed -- the executor already handles turns atomically
regardless of how they were ordered.

### Phase 3: Governance Circuits

Build the ZK circuit library for common governance patterns:
- K-of-N threshold signature verification
- Weighted threshold
- Time-locked release
- Conditional on external state (oracle attestation)

These circuits produce proofs that the executor verifies via the existing
`ProofVerifier` trait and `Authorization::Proof` pathway.

### Phase 4: Convenience APIs

- `Cell::new_governed(keys, threshold, token_id)` -- helper to create a
  governed cell with the appropriate program, VK, and permissions
- `TurnBuilder::with_governance_proof(proof)` -- helper to attach governance
  proofs to actions
- SDK support for multi-party proof generation (MPC-in-the-head or
  collaborative STARK witness generation)

---

## Cost Analysis

| Operation | Current (Owned) | Governed (Shared) | Overhead |
|---|---|---|---|
| Turn submission | 1 Ed25519 verify | 1 STARK verify | ~5-10x slower |
| Latency | Fast path (~1 RTT) | Consensus path (~3 RTT) | ~3-6x slower |
| Proof generation | None | K-of-N circuit proving | ~100ms-2s client-side |
| Storage | 32 bytes (1 key) | 32 bytes (VK hash) + VK blob | ~1-4 KB more |
| State transition | Signature check | Proof verify + program eval | ~2-3x slower |

The overhead is acceptable because:
1. Most cells remain `Owned` (fast path dominates)
2. Shared cells are minority (DAOs, treasuries, shared state)
3. Proof verification cost is amortized across the threshold (verify one proof
   regardless of K or N)
4. Consensus latency is bounded and predictable

---

## Open Questions

1. **Nonce management for shared cells**: With multiple writers, nonce ordering
   becomes the federation's responsibility (consensus assigns the nonce order,
   like Sui's `NextSharedLock`). Should the executor skip nonce checks for
   `Shared` cells and rely on consensus-assigned sequence numbers?

2. **Equivocation recovery**: Sui allows equivocated owned objects to recover at
   epoch boundaries. For shared cells, equivocation is handled by consensus
   (conflicting turns are ordered, losers fail). No recovery needed -- but
   should we charge the losing party?

3. **Access mode transitions**: Can a cell transition from `Owned` to `Shared`?
   This is dangerous (an owned cell's fast-path turns in flight could conflict
   with a new shared access). Probably require an epoch boundary for mode
   transitions, or a cooldown period.

4. **Recursive governance**: A governed cell whose authorized set includes other
   governed cells (nested DAOs). The proof must chain: "this inner DAO approved,
   and that inner DAO's approval satisfies the outer DAO's threshold." Recursive
   STARK composition handles this but adds proof complexity.

5. **Gas payment for shared cells**: Who pays the fee? Currently `turn.agent`
   pays. For shared cells, should the governed cell itself pay from its balance?
   Or should the submitter pay? (Sui: the signer always pays from an owned gas
   object.)

---

## Conclusion

The recommended approach is **Option C + access mode annotation**:

- Keep cells single-owner at the structural level
- Add `access_mode: AccessMode` for federation routing
- Model multi-owner semantics via **governed cells**: proof-authorized cells
  whose ZK circuits encode the governance policy
- Preserve the fast path for owned cells (the common case)
- Route shared-cell turns through consensus (the Sui Lutris pattern)
- Leverage existing subsystems (capabilities, delegation, conditional turns,
  composer) without modification

This design preserves pyana's core performance property (fast-path finality for
owned objects) while enabling the full spectrum of multi-owner patterns through
ZK proof authorization -- with the added benefit of privacy (anonymous credentials
over the authorized set).

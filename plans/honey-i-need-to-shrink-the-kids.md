# Honey, I Need to Shrink the Kids

How does data leave pyana? Can state get smaller? What grows forever and what can we prune?

## The Problem

| Data | Growth Pattern | Can Shrink? |
|------|---------------|-------------|
| Blocklace blocks | +1 per turn | Yes (below checkpoint) |
| Ledger cells | +1 per CreateCell | Maybe (dead cell eviction) |
| Nullifier set | +1 per note spend | Hard (needed for double-spend prevention forever?) |
| Note commitments | +1 per note create | The tree is append-only (Merkle paths break if you remove) |
| Sovereign registrations | +1 per register | Yes (TTL-based, already implemented) |
| Turn receipts | +1 per turn | Yes (archivable) |

## Ideas (Ordered by Feasibility)

### 1. State Rent / Expiry (Most Practical)

Every cell has an `expires_at` field. To stay alive, you pay rent (computrons) which extends the expiry. If you don't pay, the cell is evicted.

```rust
pub struct Cell {
    // ...existing fields...
    pub expires_at: u64,  // block height at which this cell is eligible for eviction
}
```

**Economics:**
- Rent cost scales with state size (more fields, more caps = more expensive)
- Paying rent = a turn effect that updates `expires_at` (this updates the cell → updates the commitment)
- Evicted cells: their state is dropped from the ledger. If you want it back, you must re-create it (or restore from your own backup — sovereign cells!)
- Sovereign cells are THEIR OWN RESPONSIBILITY — if you don't anchor to the federation, you can't be evicted (you don't exist on the ledger to begin with)

**The sovereignty angle:** State rent only applies to HOSTED cells (federation stores their full state). Sovereign cells store only a 32-byte commitment — effectively zero cost. This creates natural pressure toward sovereignty: if you want free storage, own your own state.

### 2. Algebraic Accumulator for Nullifiers (Research Needed)

Current: nullifiers are in a sorted Merkle tree (grows forever).

Alternative: a polynomial accumulator `A = product(alpha - h_i)` for all nullifiers h_i. The accumulator itself is ONE field element regardless of set size. Non-membership proofs are O(1) (the witness is a quotient polynomial evaluation).

**The catch:** You still need SOMEONE to maintain the full list of nullifiers to compute new witnesses. The accumulator COMPRESSES the verification, not the storage. An always-on node still needs the full set. But VERIFIERS (light clients, sovereign cells) only need the accumulator value + their witness.

**Realistic benefit:** Light clients don't need the full nullifier set. They verify non-membership via the accumulator. Storage grows at the full nodes; verification stays O(1).

We already have `AccumulatorNonRevocationAir` implementing this for revocation sets. Extending to nullifiers is mechanical.

### 3. Verkle Trees (Worth Investigating)

Verkle trees replace Merkle trees with a structure using polynomial commitments (KZG or IPA) instead of hash-based commitments. Benefits:

- **Shorter proofs:** O(log n) hashes → O(1) polynomial evaluations per path
- **Efficient updates:** can update a leaf without recomputing the full path (amortized)
- **Stateless verification:** proofs are self-contained (verifier doesn't need the tree)

**Where they'd fit in pyana:**
- Note commitment tree (currently 4-ary Poseidon2 Merkle) → Verkle
- Cell state tree (currently HashMap, no tree) → Verkle for state proofs
- Blocklace block commitments → Verkle for efficient history proofs

**The catch:** Verkle trees use KZG commitments (BLS12-381) or IPA (Pasta curves). Our primary field is BabyBear. We'd need to either:
- Use Verkle only at the "bridge" layer (for cross-chain proofs)
- Or implement Verkle in BabyBear (non-standard, research territory)

**Verdict:** Worth a spike. The Midnight integration already gives us BLS12-381 infrastructure. Verkle for the note tree specifically could reduce proof sizes dramatically for cross-chain bridges.

### 4. Recursive Proof Compression (Mina-Style)

Mina's insight: you don't need to store the full history. A single recursive SNARK proves "the current state is valid given genesis." Each block extends the proof without growing it.

We HAVE this infrastructure:
- IVC (`prove_ivc_stark`) chains sequential transitions
- STARK-in-Pickles wraps into constant-size recursive proofs
- `SovereignHistory.ivc_proof` is designed for exactly this

**The endgame:** A sovereign cell's ENTIRE history compresses to one proof. A new verifier checks one proof instead of replaying N turns. Storage = O(1) per cell regardless of history length.

**What's missing:** The IVC currently chains hashes, not full state proofs. To get Mina-style "one proof validates everything," we'd need the IVC step to INCLUDE the state transition proof (not just the hash). This is what the STARK-in-Pickles wrap gives us — each step is a Pickles proof that recursively includes the previous step.

### 5. Pruning Below Checkpoint (Immediate Win)

Blocks below the last finalized checkpoint are not needed for consensus. They're historical artifacts.

```rust
/// Called after checkpointing
fn prune_old_blocks(blocklace: &mut Blocklace, store: &Store, keep_since: u64) {
    let prunable = blocklace.blocks_before_height(keep_since);
    for block_id in prunable {
        blocklace.remove(block_id);
        store.archive_block(block_id);  // move to cold storage, or just delete
    }
}
```

Already designed (store has `prune_before()`), just needs wiring.

### 6. Note Tree Compaction

Spent notes (nullifier published) are DEAD but their commitment remains in the tree (removing would break Merkle paths for unspent notes).

Options:
- **Sparse tree:** Mark spent leaves as "empty" but keep the tree structure. New notes fill empty slots.
- **Epoch-based tree rotation:** Every E blocks, start a FRESH tree. Old trees are frozen (their root is attested). Unspent notes must migrate to the new tree within a grace period (proof of non-spending + re-commitment).
- **Verkle with deletion:** Verkle trees support efficient updates/deletions. Spent notes could actually be removed.

### 7. Computron Cost Scales with Expiry

A turn that sets `expires_at` far in the future costs more computrons (you're reserving storage for longer). Short-lived state is cheap; permanent state is expensive.

```rust
fn compute_rent_cost(state_size: usize, duration_blocks: u64) -> u64 {
    let size_factor = state_size as u64 / 32;  // per 32 bytes
    let time_factor = duration_blocks / 1000;   // per 1000 blocks
    BASE_RENT + size_factor * time_factor
}
```

This naturally incentivizes:
- Small cells (fewer fields)
- Sovereign mode (zero on-chain storage)
- Short-lived intents (auto-expire)
- Compressing history (IVC instead of storing all turns)

## What's Realistic NOW (for devnet)

1. **Blocklace pruning below checkpoint** — already designed, just wire `prune_before()`. Immediate storage savings.
2. **State rent / cell expiry** — add `expires_at` field to Cell, eviction GC task in the node. Low effort, high impact.
3. **Sovereign registrations TTL** — already implemented! (`expire_sovereign_registrations()` exists)

## What's Realistic SOON (for testnet)

4. **IVC compression for sovereign histories** — infrastructure exists, needs wallet integration
5. **Algebraic accumulator for nullifiers** — AIR exists, needs to replace the Merkle-based nullifier set
6. **Archival mode flag** — full nodes keep everything, light nodes prune aggressively

## What's Research (for mainnet)

7. **Verkle trees** (note tree, state proofs)
8. **Mina-style recursive state proof** (one proof validates entire chain)
9. **Note tree epoch rotation** (fresh tree per epoch, migrate unspent)
10. **Economic equilibrium** (rent pricing that actually balances storage cost vs utility)

## The Sovereignty Escape Hatch

The ultimate "shrinking" mechanism: **sovereign cells don't cost the federation anything.** A sovereign cell's on-chain footprint is:
- 32 bytes (commitment) when registered
- 0 bytes when deregistered (they just... leave)

If storage costs pressure hosted cells toward sovereignty, the network naturally sheds state to its rightful owners. The federation becomes lighter over time as agents take ownership of their own data. This is the "grassroots" property: the network doesn't grow proportionally to its user count because most users carry their own state.

## Nullifier Immortality

The one thing that genuinely grows forever with no escape: the nullifier set. Every spent note adds one entry that can NEVER be removed (removing enables double-spend).

Mitigations:
- **Accumulator compression** (verification is O(1), but storage still O(N) somewhere)
- **Epoch-based nullifier sets** (nullifiers expire after E epochs; notes must be "refreshed" by the holder periodically). This is controversial — it means old notes can be double-spent if the holder disappears. Maybe acceptable for devnet/testnet.
- **Bloom filters for fast rejection** (not authoritative, but saves 99% of lookups)
- **Accept it** (a million nullifiers = 32MB. That's fine for a long time.)

32 bytes × 1 million notes = 32 MB. Even at "blockchain scale" (billions of transactions), it's 32 GB. Manageable with modern hardware. Maybe this isn't actually a problem worth solving until we have REAL scale.

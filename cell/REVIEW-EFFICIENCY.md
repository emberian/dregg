# Efficiency Review: cell/, turn/, coord/, circuit/

> **Status (2026-05-20):** Issue #2 (TurnExecutor full ledger clone) is FIXED -- now uses
> journal-based undo (turn/src/journal.rs). Remaining issues (#5 capability linear scan,
> #6 Merkle root full rebuild, #8 Poseidon2 round constant regen) are still open.

## 1. Ledger HashMap<CellId, Cell> -- ACCEPTABLE WITH CAVEATS

HashMap gives O(1) lookup/insert, which is correct for random-access by CellId. However:

- **Cache locality is poor.** Cells are heap-allocated, scattered across memory. For bulk operations like `recompute_root()` that iterate all cells, a `Vec<Cell>` sorted by CellId with binary search would give better cache behavior. At 10K+ cells the difference becomes measurable.
- **Merkle recomputation dominates cost anyway** (see #6), so the HashMap overhead is secondary.

**Verdict:** Fine for now. If the ledger exceeds ~50K cells, consider a B-tree or sorted vec.

## 2. TurnExecutor Full Ledger Clone -- CRITICAL (O(n) per turn)

`executor.rs:205` clones the entire `Ledger` (snapshot) for rollback, and `apply_delta` (line 222) clones `self.cells` again. For a ledger with N cells, each turn pays O(N) clone cost regardless of how many cells the turn touches.

**Recommendation:** Use `imbl::HashMap` (persistent HAMT). Clone is O(1), structural sharing means only modified paths are copied. The `im` or `imbl` crate is purpose-built for this. Expected improvement: turn execution goes from O(N) to O(k log N) where k = cells touched.

**Impact:** HIGH. At 100K cells, each clone copies ~100K * sizeof(Cell) ~ 30MB. With HAMT, clone is a pointer bump.

## 3. CausalDag Dual Adjacency -- LINEAR IN EDGES, NOT QUADRATIC

`successors` and `dependencies` each store a `HashSet<[u8; 32]>` per node. Memory is O(V + E) where E = total edges. In practice each turn depends on 1-5 prior turns (the frontier), so E grows linearly with V. NOT O(n^2).

**Worst case:** If every turn depends on ALL prior turns (pathological), then yes, O(n^2) edges. But the protocol design (frontier-based deps) prevents this.

**Verdict:** Acceptable. Could save memory by using `SmallVec<[[u8;32]; 4]>` instead of HashSet for deps since most nodes have <5 dependencies.

## 4. Topological Sort Recomputation -- MODERATE CONCERN

`CausalDag::topological_order()` (line 272) rebuilds in-degree maps from scratch each call: O(V + E). It allocates two HashMaps.

**Recommendation:** Maintain an incremental topo order as a `Vec<[u8;32]>` updated on each `insert()`. Since new turns only depend on existing turns, the new turn always goes at the end of the topological order. Insertion is O(1) amortized.

**Impact:** MEDIUM. Only matters if `topological_order()` is called frequently. If called once at finalization, current approach is fine.

## 5. Capability Lookup -- Linear Scan is a Problem

`CapabilitySet::lookup(slot)` (line 67), `has_access(target)` (line 72), and `revoke(slot)` (line 60) all do O(n) linear scans over `Vec<CapabilityRef>`.

- `lookup` scans for a slot number.
- `has_access` scans for a target CellId.
- `revoke` uses `retain` (O(n) copy).

**Recommendation:** Replace with two indexes:
- `HashMap<u32, usize>` for slot -> vec index (O(1) lookup by slot)
- `HashMap<CellId, SmallVec<[u32; 2]>>` for target -> slots (O(1) access check)

**Impact:** LOW for small c-lists (<20 caps). HIGH if cells accumulate many capabilities (e.g., a hub cell with 1000+ capabilities).

## 6. Merkle Root Recomputation -- FULL REBUILD EVERY TIME (CRITICAL)

`Ledger::recompute_root()` (line 504) iterates ALL cells, hashes each one, sorts by CellId, pads to power-of-two, and rebuilds the entire Merkle tree from scratch. Cost: O(N log N) per mutation (sort + tree build).

Called on EVERY `create_cell`, `insert_cell`, `remove`, and `apply_delta`. The executor also calls `compute_state_hash` (line 1021) which does its own O(N) iteration.

**Recommendation:** Store a persistent Merkle tree (e.g., sparse Merkle tree or indexed Merkle tree). Updates become O(log N) -- rehash only the path from the modified leaf to the root.

**Impact:** CRITICAL. At 10K cells, each state mutation does ~10K hashes. With an indexed tree, it would do ~14 hashes. This is the single biggest performance bottleneck in the codebase.

## 7. CallForest::hash() Mutates State -- Safe but Suboptimal

`CallForest::hash()` (line 158) calls `root.compute_hash()` on each root, which recursively sets `self.hash` on all children. Multiple calls to `hash()` re-traverse the tree even when nothing changed.

**Fix:** Check if `self.hash != [0u8; 32]` (already computed) before recomputing. The invalidation on `add_child` already zeros the hash, so this is safe. Add a `if self.hash != [0u8; 32] { return self.hash; }` early return to `compute_hash`.

**Impact:** LOW-MEDIUM. Only matters for forests accessed multiple times (e.g., the executor calls `turn.hash()` which calls `call_forest.hash()` even after it was already computed during construction).

## 8. BabyBear Field Operations -- NOT Montgomery Form, No Batch Inversions

The BabyBear implementation uses direct modular arithmetic (`val % BABYBEAR_P`). For p = 2^31 - 1 (a Mersenne prime), this is actually near-optimal -- reduction is a single comparison + subtraction, not a full division. Montgomery form would add overhead for Mersenne primes.

**However:** `inverse()` uses Fermat's little theorem (30 multiplications via square-and-multiply). If multiple inversions are needed, Montgomery's batch inversion trick (1 inversion + 3n multiplications for n elements) would help. The Poseidon2 implementation does NOT use inversions in its core loop (only S-box = x^7 via squarings), so this is not currently a bottleneck.

**Round constants:** `round_constants()` and `internal_diag()` are recomputed from scratch on EVERY `permute()` call. These should be `lazy_static` or `OnceLock`.

**Impact:** MEDIUM for the round constants (30 BLAKE3 hashes per permutation, wasted). LOW for the field arithmetic itself.

## 9. Hidden O(n^2) Algorithms

1. **`CausalDag::happened_before()`** (line 172): BFS through the entire DAG history. Worst case O(V + E). Called by `are_concurrent()` which invokes it TWICE. If used in a loop over all pairs, that is O(n^2 * (V+E)).

2. **`Ledger::validate_delta()` + `apply_delta()`**: Validates the delta (iterating transfers, computing running balances), then clones the entire HashMap and re-applies everything. This is 2x the work needed.

3. **`node_frontiers.retain()` in CausalLedger** (line 456): Linear scan of the frontier vec checking membership in `causal_deps`. If both are small (typical), this is fine. If a node has a large frontier, this is O(frontier * deps).

## Summary of Priorities

| Issue | Severity | Fix Effort | Impact |
|-------|----------|------------|--------|
| Merkle root full rebuild (#6) | CRITICAL | Medium | 100-1000x for large ledgers |
| Ledger clone for atomicity (#2) | HIGH | Low (swap to imbl) | O(N) -> O(log N) per turn |
| Poseidon2 round constant regen (#8) | MEDIUM | Trivial (OnceLock) | 30 wasted hashes per permute |
| Topological sort rebuild (#4) | LOW-MED | Low | Only if called often |
| Capability linear scan (#5) | LOW | Low | Only for large c-lists |
| CallForest double-hash (#7) | LOW | Trivial | Minor constant factor |

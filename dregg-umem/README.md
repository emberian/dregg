# dregg-umem — the reusable umem-heap convention over a dregg cell

A dregg `CellState` already carries a committed `(collection, key) → value`
**heap**, sealed to the kernel's real sorted-Poseidon2 boundary root
(`dregg_cell::compute_heap_root`, the Rust shadow of the Lean `Substrate.Heap.root`,
pinned by `root_binds_get`). The substrate does not need a new store — **the cell
IS the heap.** What it lacked was a small, shared *convention* for using that heap
as a durable, passable, witnessed **execution image**.

This crate is that convention, ported from a prior imperative wrapper's
record-laying + time-travel logic onto our native cells, so the boundary is the
kernel's real Poseidon2 root and not a stand-in.

## The four verbs, over `CellState` + `compute_heap_root`

| verb | function | what it does |
| --- | --- | --- |
| **lay / open** | `lay` · `lay_record` · `open` · `open_record` | lay a record into a heap collection as length-delimited 32-byte leaves; reassemble it back (fail-closed on a truncated laying) |
| **boundary_root** | `boundary_root` · `boundary_root_hex` · `binds` | the cell's committed Poseidon2 heap root; `binds` is the `root_binds_get` tooth over a record |
| **fork** | `fork` · `fork_into` | copy the committed heap image into a second cell — divergent copies from one root |
| **checkpoint / restore** | `Checkpoint::capture` · `restore` · `Timeline` | reify the heap to a checkpoint; restore it (fail-closed if the image does not reproduce its root); `Timeline::time_travel` rolls back to an earlier committed root |

The heap leaf-set is grow-only, so the I-confluent `dregg-merge` runtime applies
unchanged: `merge::grow_set` gives a content-addressed `GrowSet` view of a cell's
laid records, and two forks' record-sets merge by set union with no coordination.

## Two future consumers (not refactored in this lane)

- **`starbridge-execution-lease`** — its `EXEC_COLL` durable execution image is a
  laid umem record + a boundary root; its `advance_checkpoint` / `mirror_checkpoint`
  are `Checkpoint::capture` + `restore` over the cell heap.
- **`starbridge-vat`** — a vat is a Dregg Computer: **sleep = `Checkpoint::capture`**,
  **wake = `restore`**, **fork = `fork_into`** of the execution-image cell.

Both hand-roll this today. Wiring them over `dregg-umem` is a deliberate follow-up;
this crate lands the convention + its tests first, so each swap is a mechanical,
separately-reviewable change.

## The honest boundary

The verified boundary is the OFF-chain half: real Poseidon2 root, re-derivable and
fail-closed on restore. The in-circuit witness that a light client sees the
checkpoint move — and that a free merge preserved the invariant — stays the circuit
swarm's VK-epoch (the `MergeRefinesConfluence` weld `dregg-merge` already names).
This crate adds no Lean theorem; it is the executable convention over the cells the
theorems already pin.

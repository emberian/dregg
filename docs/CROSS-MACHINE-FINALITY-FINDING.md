# Cross-machine finality stall (live 2-machine n=4, gate-ON) — root cause

**Setup.** `~/n4fed-v2`, gate-ON. hbox `192.168.50.39` = Linux **release** node +
Linux Lean seed; nextop `192.168.50.130` = Darwin **debug** node + Darwin Lean
seed. The DAGs converge identically; the node's own differential fired three
alarms — a Rust↔Lean tau-order set divergence (`rust_len=0`), a producer-side
Lean↔Rust root disagreement ("THE SWAP authority inversion"), and a reorg-by-
catchup "PREFIX SHIFTED" storm — while `latest_height` sat near 1.

**Verdict (one line).** This is the **`docs/N3-ROOTCAUSE.md` /
`docs/VERIFIED-GATE-PERF.md` class recurring cross-machine**: the O(history)
verified-Lean tau-order FFI is recomputed from scratch on every finality poll,
and under genuine cross-machine catch-up churn its cross-poll cache is busted on
every poll, so committed-turn throughput falls arbitrarily far below block
production and finality **crawls** rather than deadlocks. It is **NOT**
cross-platform Lean non-determinism — the two verified Lean seeds (Linux release
vs Darwin debug) are **byte-identical on committed state** (the decisive cell-root
comparison below). The `rust_len=0` divergence and the SWAP root inversion are
**real but secondary**: neither is on the commit path that decides state, and
neither corrupts it.

---

## The decisive experiment: cross-machine committed state is IDENTICAL

`GET /api/cell/0a0b3c0b…` (the faucet recipient funded 5000) on BOTH machines:

| node | balance | nonce | `state_commitment` |
|---|---|---|---|
| .39 (Linux **release** + Linux Lean) | 5000 | 0 | `eff88f0279d03efa64d0966479b36df4f67ad3a9d5392831ae2f17bf66db2b1a` |
| .130 (Darwin **debug** + Darwin Lean) | 5000 | 0 | `eff88f0279d03efa64d0966479b36df4f67ad3a9d5392831ae2f17bf66db2b1a` |

Identical. And the receipt streams agree on post-state per turn — e.g. turn
`82d2da02…` → `post_state c9c81eb3…` on both; turn `5232c5aa…` → `dd214079…` on
both. Those committed roots are exactly the `lean_root` values the SWAP-inversion
error prints (`lean_root=c9c81eb3…`, `lean_root=dd214079…`).

**Therefore the two Lean seeds are DETERMINISTIC across Linux/Darwin and
release/debug.** The stall is not state non-determinism; it is the reorg-storm /
verified-gate-perf path. (Had the roots differed, this would have been a real
cross-platform verified-executor determinism bug — it is not.)

---

## The stall is a CRAWL, not a deadlock (and consensus itself is healthy)

Sampled live during this investigation:

| observation | value |
|---|---|
| `latest_height` at the finding | 1 (dag 243, blocks 967) |
| `latest_height` now (both nodes) | **3** (dag 382, blocks 1501) |
| dag_height movement over ~2 min while height flat | 317 → 382 (**+65 blocks**) |
| newest committed receipt timestamp vs now | ~14 min stale while the DAG kept producing |
| node0 finalized-order length (`lean_len`) over the run | 23 → 1344 and climbing, monotone |
| `prefix_shifts` | 27 → 36 (visible reorg-by-catchup, absorbed) |

`latest_height` = the height of the latest **attested root**
(`node/src/api.rs:1924`), which advances **+1 per committed finalized turn**
(`node/src/blocklace_sync.rs:4789-4869`, `new_height = attested_height + 1`). So
height tracks committed *turns*, not blocks. The DAG (heartbeat/ack/round blocks)
races ahead at ~30 blocks/min while committed-turn height is nearly flat — the
exact signature of `docs/VERIFIED-GATE-PERF.md`: **the finalized prefix cannot
reach the frontier turn in-window because the per-poll verified-order cost has
outgrown the block-production rate.** Consensus (produce/deliver/cite/poll) is
healthy — the DAGs converge identically on all four nodes; it is the (e) verified
tau-order GATE that throttles, precisely as the N3 post-mortem found.

---

## 1. The Rust-executor root divergence ("THE SWAP authority inversion")

**What fires.** `node/src/executor_setup.rs:155-166`, target
`dregg::lean_shadow::producer`: on a covered turn the verified Lean executor and
the demoted Rust reference commit **different roots** (`lean_root ≠ rust_root`),
for agents `4a8882bb` and `12d4e7e6`.

**Why (grounded).** `produce_via_lean` (`exec-lean/src/lean_apply.rs:1518-1616`)
hands BOTH executors the **same pre-state `ledger`**: it runs the Lean FFI first
(`:1545`, reconstituting the post-state from the *current* pre-state), snapshots
`pre_root` (`:1564`), then runs the Rust executor **in place on that same ledger**
(`:1574`). `rust_agreed = lean_committed == rust_committed && lean_root ==
rust_root` (`:1577`). Because both start from an identical pre-state, a
`lean_root ≠ rust_root` is a **genuine executor-level disagreement** on a covered
turn — the Rust reference computes a different post-root from the same input.

**Real Rust-executor bug, or stale read during reorg?** **A real Rust-executor
faithfulness discrepancy, not a stale read.** Both executors see the same ledger
snapshot, so there is no stale-vs-fresh asymmetry between them. What the reorg
*does* do is cause covered turns to be (re)executed more often — including the
same logical turn re-carried in a fresh block (visible as the DUPLICATE receipt on
.39: `chain_index` 2 and 3 both carry turn `5232c5aa…`, pre `3aa8033d…`, post
`dd214079…`) — which surfaces the discrepancy repeatedly. This is exactly the
residual THE SWAP exists to catch: on the root-agreeing ("covered") set a Lean↔Rust
disagreement is **by construction the Rust path being wrong**; the verified Lean
verdict is installed unconditionally (`:1587-1589`) and Rust is never allowed to
override it (`:151-166`). The committed `lean_root` matches both the receipts and
the cross-machine cell state above, so **state is not corrupted and cross-machine
safety holds**. The finding is that the covered-set characterization
(`lean_shadow::forest_is_root_agreeing`, `:1527`) has a residual hole for these two
agents' turns — a Rust-executor bug to capture, **not** a consensus defect.

## 2. Rust `ordering::tau` returning 0 while verified Lean returns hundreds

**What fires.** `node/src/blocklace_sync.rs:1163-1172`: the Rust `ordering::tau`
and the verified Lean `dregg_tau_order` finalize different `(creator, seq)` sets.
On node0 the trace is striking: `rust_len = 0` for ~8 minutes while `lean_len`
climbs 23 → 636, then Rust *overshoots* (`lean=891 rust=1187`, later converging
`lean=1344 rust=1318`).

**Why (grounded) — the two orders run on DIFFERENT laces.** Both implementations
use the *same* DAG-depth round recurrence `round(b) = 1 + max(round(preds))`
(`blocklace/src/ordering.rs:86-146`;
`metatheory/Dregg2/Distributed/BlocklaceFinality.lean:12,74-103` states the same
recurrence). But in `poll_finalized_blocks`:

- the **verified Lean** order is computed on the **original full lace**
  (`compute_order(&lace_ffi …)`, a clone of the real lace, `:1094-1107`), whereas
- the **Rust differential** runs on a **rebuilt projection**,
  `build_ordering_blocklace(&lace)` (`:1037`, def `:1600-1652`), which re-inserts
  blocks **sorted by `(seq, creator)`** and keeps **only predecessors already
  inserted** (`filter_map(|p| finality_to_ordering.get(p))`, `:1620-1624`).

When `seq` order ≠ topological order — the **cross-machine catch-up case**, where a
lagging creator's late block has a LOW `seq` but a HIGH DAG-depth round — the
seq-sorted rebuild drops predecessor edges (the referenced block is not yet
inserted), collapsing the projected DAG depth. Rust's `find_all_final_leaders`
(`ordering.rs:350-405`) then finds **no super-ratified leader** (`rust_len=0`)
until the frontier fills in, and over-includes once it does. Single-machine on a
clean round-synchronous DAG, `seq` ≈ round ≈ topo order, no edges drop, and
Rust == Lean — exactly why `docs/N3-ROOTCAUSE.md` saw **"no divergence, ever."**

> **Correction, 2026-11-13 (dregg issue #100).** The reading above cleared the Lean side too
> quickly. The Lean order did receive every edge, but its ROUND MAP folded the wire's blocks in
> the same `(seq, creator)` order and skipped predecessors it had not folded yet
> (`BlocklaceFinality.roundOfStep`'s `filterMap`). So in exactly this catch-up case the lagging
> creator's late block got round 1 in the AUTHORITY as well: one block's round wrong rather than
> the whole projection's depth, which is why Lean still returned an order. If that creator led
> the wave it rejoined in, the verified rule never anchored that wave. The Lean fold is now a
> Kahn enumeration (`topoLace`), with the round proved independent of the listing
> (`roundOf_perm`).

**Crucially this is the DIFFERENTIAL sibling, not the authority.** The node
finalizes over the **Lean** order (`ordered_from_lean = true`, `:1181`;
`ordered = lean_order`, `:1182`). So `rust_len=0` does **not** withhold any block
from execution — it is a false-alarming cross-check produced by a lossy rebuild,
currently drowning the logs (301 divergence lines) and masking real signal.

## 3. The stall cause: reorg-storm × verified-gate O(history) perf (NOT non-determinism)

Test (b) — cross-machine state non-determinism — is **refuted** by §"decisive
experiment": both seeds commit identical roots. The stall is (a): the
`docs/VERIFIED-GATE-PERF.md` cost, amplified cross-machine.

- The finality executor is a single serial task; each poll clones the whole lace
  and runs the O(history) verified-order FFI before the next poll can start
  (`docs/VERIFIED-GATE-PERF.md` §1; `poll_finalized_blocks` `:948-1138`).
- A cross-poll cache exists to skip the FFI when the lace is unchanged
  (`last_order_fingerprint`, `:1063-1135`), but it is **all-or-nothing on an exact
  block-id-set fingerprint**. Under continuous cross-machine catch-up the lace
  changes every poll, so the fingerprint MISSES every poll → the full O(n²) FFI
  runs every poll. As `lean_len` grows 23 → 1344 the per-poll wall grows with it;
  the observed poll spacing stretched from ~8 s early to ~40-45 s late.
- Result: committed-turn throughput falls below the ~30 blocks/min production
  rate; the finalized prefix cannot reach new frontier turns in-window, so
  `latest_height` crawls (1 → 3 over the window) while the DAG races (blocks 967 →
  1501). The newest committed turn is ~14 min stale while the DAG keeps producing.

## 4. Is the reorg-storm expected, or a bug? — expected shape, wedge-free handling

`metatheory/Dregg2/Consensus/TauPrefixMonotone.lean` proves tau's finalized prefix
is stable only *conditionally* and exhibits an honest catch-up counterexample: a
lagging validator's late wave-end block ratifies an already-final leader and sorts
**mid-prefix**. So *some* prefix shifting is expected. The live handling is
**sound and does not wedge**: the executor tracks executed blocks **by identity**,
not by index (`node/src/execution_cursor.rs:98-131`) — `pending(&ordered)` is a set
difference walked in the *current* tau order, so every finalized block executes
**exactly once** regardless of how the prefix re-sorts, and `observe_order`
(`:138-146`) only *reports* the shift. The 27→36 shifts are the counterexample
happening live and being absorbed, **not** a wedge. (The duplicate receipt in §1
is a *turn* re-carried in a distinct block id — a distinct block that executes once
— not the same block re-executing.)

So the stall is **not** the prefix-shift handling failing; it is the per-poll
verified-order cost the shifts *ride on top of* (each shift changes the lace →
cache miss → full recompute).

---

## Fix direction (DESIGN ONLY — do NOT fire; consensus is ember's call)

1. **Make the verified tau-order INCREMENTAL across polls** (the direct fix; N3
   lever 1 finished). Finality is monotone and the lace only grows, but the
   cross-poll cache is exact-match on the whole block-id set, so catch-up churn
   busts it every poll. Reuse prior verified work on lace *growth* (append-friendly
   memo / verified prefix reuse) instead of all-or-nothing fingerprint equality, so
   the per-poll cost is O(delta), not O(history). This is what lifts committed-turn
   throughput back above block production.

2. **Un-stall the serial executor from the FFI** (N3 lever 2). Bound the
   verified-order FFI per poll (timeout → use the already-computed order for that
   poll, or run the verified order off the critical path as a cross-check rather
   than the awaited authority) so one slow poll cannot freeze *all* finalization.

3. **Fix the Rust DIFFERENTIAL, not consensus** (observability). Have
   `build_ordering_blocklace` insert in **topological** order (not `(seq, creator)`)
   so the Rust sibling runs on the same edge set as the Lean authority — eliminating
   the spurious `rust_len=0` divergence that is currently false-alarming 300× and
   hiding real signal. Pure cross-check/observability change; not on the commit
   path.

4. **Capture the SWAP-inversion turns as a golden** and shrink them in
   `exec-lean`'s divergence-finder (`rust_lean_divergence_finder.rs`): the
   root-agreeing set characterization has a residual hole for agents `4a8882bb` /
   `12d4e7e6`. Lean-safe (Lean wins, state uncorrupted), but a genuine Rust-executor
   faithfulness bug to close. Lean/verification-owner's call.

**None of the above is a consensus-rule change.** The verified rule and its
cross-machine determinism are intact; the defect is per-poll *performance* under
reorg churn plus two loud-but-secondary differential alarms.

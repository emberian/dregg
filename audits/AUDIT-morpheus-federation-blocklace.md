# Audit: morpheus / federation / blocklace

## Scope

Determine whether `federation/` and `blocklace/` are redundant, complementary, or one is dead, and identify safely removable "morpheus" cruft.

Excluded from edits (other agents working): `circuit/`, `turn/`, `protocol-tests/`, `verification/`, `spec/`, `demo/sdk-consensus/`, `observability/`, and broad changes to `cell/`, `node/`, `sdk/`, `apps/`.

## 1. "morpheus" reference inventory

Grep across `*.rs`, `*.toml`, `*.md` (case-insensitive) — 69 hits total. Bucketed:

### Active code (in-scope for cleanup)

| File                              | Hits | Nature                                                        |
| --------------------------------- | ---: | ------------------------------------------------------------- |
| `federation/src/lib.rs`           | 4    | doc comments + 1 `#[cfg(feature = "morpheus")]` gate          |
| `federation/src/node.rs`          | 1    | doc comment                                                   |
| `federation/src/transport.rs`     | 1    | doc comment on `NetworkConsensusNode`                         |
| `federation/src/bin/demo.rs`      | 2    | log strings ("Morpheus: block finalized…")                    |
| `node/src/blocklace_sync.rs`      | 3    | comparison comments explaining "replaces Morpheus"            |
| `node/src/state.rs`               | 1    | comment on `consensus_queue` field                            |
| `demo/src/federation.rs`          | 1    | module-level comment                                          |
| `docs/galaxybrain-pyana.md`       | 1    | architectural prose                                           |
| `docs/protocol-sketch.md`         | 2    | architectural prose                                           |
| `docs/midnight-comparison.md`     | 1    | comparison table cell                                         |

### Historical / out-of-scope (do not touch)

- `.docs-history-noclaude/federation-architecture.md` (29) — historical decision record (KEEP per instructions)
- `.docs-history-noclaude/fast-path-design.md` (12)
- `.docs-history-noclaude/plans/consensus-architecture-v2.md` (3)
- `.docs-history-noclaude/plans/devnet-upgrade.md` (2)
- `.docs-history-noclaude/proof-carrying-state.md` (2)
- `old-docs/protocol-sketch.md` (2), `old-docs/midnight-comparison.md` (1), `old-docs/galaxybrain-pyana.md` (1) — explicitly old

## 2. `federation/` vs. `blocklace/`

**Not the same thing.** They are partly overlapping but mostly complementary.

### `pyana-blocklace` — the LIVE consensus engine

DAG-based BFT (Cordial Miners / tau ordering) used by the running node.

Modules: `addressing`, `constitution`, `cross_reference`, `delegation`, `dissemination`, `finality`, `ordering`, `pyana_bridge`.

Live integration: `node/src/blocklace_sync.rs` imports `Block`, `BlockId`, `Blocklace`, `FinalityLevel`, `tau`, `Constitution`, etc. CLI defaults to `--consensus blocklace`, which is the **only** value accepted by `node/src/main.rs:498-527` (any other string is a hard error).

### `pyana-federation` — TWO disjoint sub-roles

(a) **Live utilities still used by the running node**:

- `solo::FederationMode`, `SoloConsensusState`, `NullifierLog` — single-node devnet path. Used by `node/src/main.rs`, `node/src/state.rs`, `node/src/api.rs`.
- `quorum_threshold(n)`, `fault_tolerance(n)` — canonical BFT formulas, used by `node/src/genesis.rs:127` and (transitively) by `pyana-blocklace`'s finality logic.
- `threshold` and `threshold_decrypt` — threshold encryption / key-share types. Used by `node::state` (`KeyShare`, `DecryptionShare`).
- `checkpoint`, `revocation`, `epoch`, `types::*` — checkpoint and AttestedRoot types, used by `node::api`, `node::state`, `wire::federation_bridge`.

(b) **Dead Morpheus-shaped BFT simulation**:

- `pyana_federation::node` module — `ConsensusConfig`, `ConsensusState`, `ConsensusOrchestrator`, `Federation`, `FederationNode`. Synchronous simulation harness.
- `pyana_federation::transport` — `NetworkConsensusNode`, `TcpFederationTransport`, propose/vote/finalize pacemaker.
- `pyana_federation::network` — `#[cfg(feature = "morpheus")] pub mod network` with **no `morpheus` feature defined** in `federation/Cargo.toml`. **Unreachable**.

The dead simulation is exercised by test harnesses (`tests/src/byzantine.rs`, `teasting/src/harness.rs`, `federation/tests/tcp_consensus.rs`, `federation/src/bin/{demo,node}.rs`, `federation/benches/consensus_bench.rs`, `wire/src/{federation_bridge.rs,bin/multi_node.rs}`, `demo-agent/examples/federation_*.rs`, `demo/src/*.rs`). None of these are on the live node path. They are kept because tests and examples link them, not because production needs them.

## 3. Live consensus pathway from `node` startup

`node/src/main.rs::run_node`:

1. Parse CLI; `--consensus blocklace` (default and only accepted value).
2. Initialize `state::NodeState` (holds `solo_consensus: Option<SoloConsensusState>`, `federation_mode`, blocklace store).
3. Set `FederationMode::Solo` or `Full`. In Solo, instantiate `pyana_federation::solo::SoloConsensusState` — single-node sequencing.
4. Spawn `tokio::spawn { blocklace_sync::run_blocklace_sync(state, gossip_port, auto_approve_joins) }` (lines 498–518).
5. `run_blocklace_sync` runs the live BFT loop via `pyana_blocklace::{finality, ordering::tau, dissemination, constitution}`.

Wire path is identical: there is no `NetworkConsensusNode` (Morpheus) in the live node. The `wire::federation_bridge` module that depends on it is only reachable via the `wire::bin::multi_node` demo binary and bridge tests, not via `node`.

## 4. `wire/` morpheus exposure

No literal "morpheus" string in `wire/`. The `wire::federation_bridge` module wraps `pyana_federation::NetworkConsensusNode` (the Morpheus simulation) and is **functionally** the wire-level adapter for the dead path. It compiles (the simulation types are unconditionally exported) but is not on the live node hot path. Rename/migrate of this bridge is **out of scope** for this iteration per instructions.

## 5. Recommended cleanup

### Phase 2 — DELETE (this iteration)

Strict criteria: unreferenced AND not behind a live feature flag AND build still green AND not historical-record docs.

1. **`federation/src/network.rs`** — Gated behind `#[cfg(feature = "morpheus")]` and no `morpheus` feature in `federation/Cargo.toml`. No callers (`grep crate::network -r federation/` empty). 253 lines of pure dead code.
2. **`pub mod network;` declaration in `federation/src/lib.rs:62-63`** — removed alongside `network.rs`.
3. **Doc/comment de-morpheusing** (text-only, no API change): retitle "Morpheus" to "BFT" / "blocklace" in:
   - `federation/src/lib.rs` (4 doc-comment hits)
   - `federation/src/node.rs:6`
   - `federation/src/transport.rs:744`
   - `federation/src/bin/demo.rs:143,253` (log strings)
   - `node/src/blocklace_sync.rs:3,64,434` (already comparative — say "Replaces the prior BFT" instead of "Morpheus")
   - `node/src/state.rs:84` (comment on `consensus_queue`)
   - `demo/src/federation.rs:13` (referenced `pyana_federation` crate description)
   - `docs/galaxybrain-pyana.md:214`, `docs/protocol-sketch.md:21,122`, `docs/midnight-comparison.md:12`

### RENAME / MIGRATE (deferred — note only)

Out of scope this iteration:

- Delete or refactor `pyana_federation::node` (`ConsensusOrchestrator`/`Federation`/`FederationNode`), `pyana_federation::transport` (`NetworkConsensusNode`/`TcpFederationTransport`), and downstream consumers (`wire::federation_bridge`, `wire::bin::multi_node`, `tests::byzantine`, `teasting::harness`, `demo-agent/examples/federation_*`, `demo/src/{federation,revocation,trace,verifier,main}.rs`, `federation/src/bin/*`, `federation/tests/tcp_consensus.rs`, `federation/benches/consensus_bench.rs`). These would need a follow-up: either re-target onto blocklace primitives or excise the test/demo harnesses entirely. Several thousand lines, behavioural risk → not a "clear stale reference" change.
- Split `pyana-federation` into `pyana-federation-utils` (solo, threshold, threshold_decrypt, checkpoint, revocation, quorum math) and remove the dead `pyana-federation::node/transport` consensus simulator.
- Move `solo`, `threshold`, `threshold_decrypt`, `checkpoint`, `revocation`, `epoch` and `quorum_threshold` out of the crate that's named after a dead protocol.
- `.docs-history-noclaude/federation-architecture.md` is *the* historical record (it explicitly says "Morpheus adapter is dead code") and stays per instructions.

### KEEP (do not edit)

- All `.docs-history-noclaude/` and `old-docs/` references — historical record.
- `pyana_federation::{solo, threshold, threshold_decrypt, checkpoint, revocation, epoch, quorum_threshold, fault_tolerance}` — live utilities.

# AUDIT-CRATE-DISPOSITION.md

Read-only assessment of the `audit/` workspace member (`pyana-audit`),
following up on `BACKWATER-CRATES-AUDIT.md` which flagged the crate as
dormant-but-well-formed. The designer needs to decide: revive it as a
load-bearing component, delete it, or merge its contents into a sister
crate.

This document covers the five sections requested and ends with a single
recommended verdict.

---

## §1 — What's in `audit/`

### Cargo footprint

`audit/Cargo.toml` is minimal:

```toml
[package]
name = "pyana-audit"
version.workspace = true
edition.workspace = true

[dependencies]
pyana-commit = { path = "../commit" }
blake3       = "1"
serde        = { version = "1", features = ["derive"] }
```

Three deps. No `getrandom`, no `rand`, no curves, no STARK/Kimchi
machinery. The crate sits below most of the workspace and depends only
on `commit` (for `hash_leaf`, `hash_node`, `empty_hash_at_depth`,
`HASH_ARITY`) and blake3 + serde.

### Stated purpose (from `lib.rs` doc comment)

> `pyana-audit`: Verifiable token audit trail for the pyana ZK token
> system. … privacy-preserving audit trail that proves token usage
> history without revealing the full history to the auditor.

It claims to deliver:

- **Usage events** — immutable records of token presentations.
- **Append-only audit log** — Merkle-committed sequence.
- **Audit receipts** — proofs of inclusion at a specific log root.
- **Privacy-preserving proofs**: `CountProof`, `RangeProof`,
  `ConsistencyProof`, `BudgetProof`, plus `LastUseProof`.
- **Budget enforcement** — integrates the audit log with usage limits
  via `BudgetEnforcer`.

### Actual surface

Five modules, all `pub`, plus an integration-test module:

| File          | LOC  | Purpose                                                                                       |
|---------------|-----:|-----------------------------------------------------------------------------------------------|
| `lib.rs`      |   85 | Doc + re-exports.                                                                             |
| `event.rs`    |  170 | `UsageEvent { token_id, timestamp, action_hash, verifier_id, sequence }`, `AuditReceipt`, `InclusionProof` (4-ary Merkle inclusion). |
| `log.rs`      |  784 | `AuditLog` — append-only 4-ary Merkle tree (depth 12 = ~16M event capacity), incremental cached interior nodes, `LogSnapshot`, `BridgeHash`, `TimestampWitness`, retention-bounded historical roots. |
| `proofs.rs`   |  542 | `CountProof`, `RangeProof`, `LastUseProof`, `ConsistencyProof`, `BudgetProof` — all with `.verify()` methods and independent unit tests. |
| `budget.rs`   |  394 | `BudgetSpec { limit, window }`, `BudgetEnforcer { token_id, budget, log }`, `BudgetExhausted`, `WindowInfo`. Total and windowed budgets. |
| `tests.rs`    |  487 | End-to-end integration tests (12 named scenarios).                                            |

Re-exports at crate root: `BudgetEnforcer`, `BudgetExhausted`,
`BudgetSpec`, `AuditReceipt`, `InclusionProof`, `UsageEvent`,
`AuditLog`, `LogSnapshot`, `BudgetProof`, `ConsistencyProof`,
`CountProof`, `LastUseProof`, `RangeProof`.

### Key implementation notes

- **4-ary Merkle tree** with depth 12 (matches `pyana-commit::hash`
  constants `HASH_ARITY = 4`, and `empty_hash_at_depth` precomputes the
  empty-subtree hashes).
- **Incremental append**: `AuditLog::append` recomputes only the
  O(log₄ N) path from new leaf to root; interior nodes are cached in
  `tree_levels: Vec<Vec<[u8; 32]>>`. There is a `#[cfg(test)]`
  `rebuild_tree_and_verify` that proves the cache matches a from-scratch
  recomputation across multiple growth boundaries (1, 4, 16, 64, 100).
- **Historical roots** are retained up to a configurable limit
  (`DEFAULT_HISTORICAL_ROOTS_LIMIT = 10_000`); older roots are pruned
  with an offset so `historical_root(size)` still maps correctly.
- **`AuditReceipt`** captures the inclusion proof *at the moment of
  append* (`log_root_after`). Tests verify the receipt continues to
  verify against its recorded root after more events are appended —
  this is the non-repudiation hook.
- **`BudgetEnforcer`** binds a token to a budget and an audit log;
  `record_use` first calls `can_use(now)` and only appends to the log
  if the budget permits. Windowed budgets use epoch-aligned windows
  (`(now / window_secs) * window_secs`).
- **Privacy claim**: `CountProof` carries `(global_index, leaf_hash,
  inclusion_proof)` triples — i.e., it does *not* reveal `action_hash`
  or `verifier_id` of each event, only that K events for `token_id`
  exist in a log whose root matches. The index-commitment binds the
  proof's index set so a verifier cannot silently drop entries.

The whole crate is no-std-clean in spirit (only `std::collections` and
`std::time::Duration`), no async, no globals, no I/O. It is a pure
data-structures-and-proofs crate.

---

## §2 — `audit::budget` vs `coord::budget`

The backwater audit claimed `audit::budget` is a duplicate of
`coord::budget`. **They are not duplicates.** They are namesakes
operating on disjoint domains, sharing no types, no traits, and almost
no concepts.

### Side-by-side

| Aspect                | `audit::budget::BudgetEnforcer`                           | `coord::budget::BudgetCoordinator`                        |
|-----------------------|-----------------------------------------------------------|-----------------------------------------------------------|
| **Subject**           | A single token (`[u8; 32]` token_id)                      | A single agent's resource balance (`CellId`)              |
| **Resource**          | Usage *count* (number of presentations)                   | Any fungible quantity (computrons, API calls, bytes, …)   |
| **Distribution**      | One enforcer, one log, no parties                         | Sharded across N silos with Byzantine tolerance f         |
| **Hot-path check**    | `can_use(now)` against an in-memory log count             | `try_debit(silo, amount, digest)` against a local slice   |
| **Coordination**      | None (single-writer enforcer)                             | Periodic rebalance with Ed25519-signed `SpendingCertificate`s |
| **Abort recovery**    | N/A                                                       | `FastUnlockManager` with `UnlockVote` / `UnlockCertificate` quorum |
| **Underlying state**  | 4-ary Merkle log (`pyana_commit::hash`)                   | `HashMap<SiloId, BudgetSlice { ceiling, spent, debits }>` |
| **Audit story**       | First-class: every debit produces an `AuditReceipt` with inclusion proof | None; spending certificates are only inputs to rebalance |
| **Proof artifacts**   | `BudgetProof`, `CountProof`, `ConsistencyProof`, `RangeProof`, `LastUseProof` | `SpendingCertificate`, `UnlockCertificate` (purpose: liveness/safety, not third-party audit) |
| **Byzantine model**   | Single trusted writer; the proofs defend against a *lying enforcer* to a *third-party auditor* | f-of-3f+1 silos may be Byzantine; protocol bounds maximum overspend |
| **Window semantics**  | Epoch-aligned time windows                                | Epoch counter is `BudgetVersion` (monotonic, bumped on rebalance) |
| **Lives under**       | Token / authorization layer                               | Coordination / atomic-turn layer                          |
| **External signature**| None — proofs verify against a published Merkle root      | Ed25519 (`ed25519_dalek`) on every certificate            |

### What they share

Almost only the name `BudgetSpec`. And even there, the *type* is
different:

- `audit::budget::BudgetSpec { limit: u64, window: Option<Duration> }`
- `pyana_token::traits::BudgetSpec { … }` (used by `token`, `apps/*`,
  `demo-agent` — *not* by `coord`)
- `coord::budget` has no `BudgetSpec` at all; it has `BudgetSlice`,
  `BudgetCoordinator`, `BudgetVersion`, `ResourceAmount`.

So there are actually *three* "budget" namespaces in the tree
(`audit::budget`, `coord::budget`, `pyana_token::traits`), and they
slice the problem at different layers:

- **`token::traits::BudgetSpec`** — declarative policy stated in a
  capability/macaroon.
- **`audit::budget::BudgetEnforcer`** — verifier-side enforcement of
  *that* policy, with cryptographic non-repudiation of every
  presentation.
- **`coord::budget::BudgetCoordinator`** — silo-side enforcement of an
  *agent's* resource balance, with Byzantine-tolerant local debits and
  periodic reconciliation.

### Verdict on the duplication claim

The backwater audit (line 1057) said:

> The two BudgetEnforcer-shaped types ought to live together.

I disagree with that recommendation. The shapes are superficially
similar (`limit`, `spent/uses_consumed`, `remaining()`) but the
operational semantics are unrelated:

- `audit::budget` is **about producing a proof an auditor will trust**.
- `coord::budget` is **about not blocking the hot path on consensus**.

Merging them would conflate "what did this token do" with "how much of
my balance has each replica burned" — these are independently useful
abstractions. If anything, the `pyana_token::traits::BudgetSpec` should
be the *one* `BudgetSpec` shared by both: the token says "limit 5 per
hour" (token traits), the verifier enforces it and proves it
(audit::budget), the coordinator allocates the agent's resource pool
across silos (coord::budget).

The duplication that *does* exist is between `audit::budget::BudgetSpec`
and `pyana_token::traits::BudgetSpec`. That's a different cleanup.

---

## §3 — Reverse-dep check

`grep -rn "pyana-audit\|pyana_audit" --include="*.toml" --include="*.rs"`
turns up exactly these consumers across the workspace:

**Cargo manifests:**

- `audit/Cargo.toml` — the crate itself.
- `store/Cargo.toml` — `pyana-audit = { path = "../audit", optional = true }`,
  gated behind the `audit-bridge` feature.

**Source files (excluding `audit/` itself):**

- `store/src/audit.rs` — defines `StoredAuditEvent` (a postcard-
  serializable mirror of `pyana_audit::event::UsageEvent`) and an
  `AuditBridge` with two methods: `persist_audit_log_range(&log,
  from, to)` and `persist_audit_log(&log)`. Both copy from the
  in-memory `AuditLog` into redb storage.
- `store/src/lib.rs` — one doc-comment reference.
- `tests/src/budget.rs` — imports `pyana_audit::proofs::*` and
  `pyana_audit::{AuditLog, BudgetEnforcer, BudgetExhausted,
  BudgetSpec, LogSnapshot, UsageEvent}`.

**Critical: `tests/src/budget.rs` is broken at the workspace level.**
`tests/Cargo.toml` does NOT list `pyana-audit` as a dependency:

```toml
[dependencies]
pyana-circuit = { path = "../circuit" }
pyana-turn    = { path = "../turn" }
pyana-cell    = { path = "../cell" }
pyana-sdk     = { path = "../sdk" }
pyana-types   = { path = "../types" }
pyana-bridge  = { path = "../bridge" }
pyana-dsl-runtime = { path = "../pyana-dsl-runtime" }
token         = { path = "../token", ... }
blake3        = "1"
getrandom     = { workspace = true }
postcard      = { version = "1", features = ["use-std"] }
proptest      = { workspace = true }
```

…yet `tests/src/main.rs` has `mod budget;`. This means either (a) the
`pyana-tests` crate currently doesn't compile, or (b) `mod budget;` was
recently added without updating Cargo.toml. I confirmed the workspace
itself cannot resolve (`cod/Cargo.toml` is missing per `git status`
exclusion noise), so I can't run `cargo check -p pyana-tests` cleanly
to settle this empirically — but the manifest is missing the dep and
the file unambiguously requires it.

**Effective live reverse-dep count: ONE.** Just `store/`, behind the
`audit-bridge` cargo feature. The `tests/src/budget.rs` file is either
dead code that doesn't compile, or it's a tells-us-something-is-rotten
signal that even the protocol-test layer doesn't actively exercise the
audit crate.

No app under `apps/*` depends on `pyana-audit`. No node path
(`node/`, `discharge-gateway/`, `cli/`, `demo/`, `demo-agent/`) imports
it. The verifier crate doesn't use it. No SDK surface, no wire format.

### What the existing reverse-dep does

`store::audit::AuditBridge::persist_audit_log` walks the in-memory
`AuditLog`'s events and stuffs them into redb as `StoredAuditEvent`s.
That is **the entirety of the dependency**:

```rust
pub fn persist_audit_log_range(
    &self,
    log: &pyana_audit::AuditLog,
    from_index: u64,
    to_index: u64,
) -> Result<()> { … }

pub fn persist_audit_log(&self, log: &pyana_audit::AuditLog) -> Result<u64> { … }
```

`store::audit::StoredAuditEvent` is a structural copy:

```rust
pub struct StoredAuditEvent {
    pub global_index: u64,
    pub token_id: [u8; 32],
    pub timestamp: i64,
    pub action_hash: [u8; 32],
    pub verifier_id: [u8; 32],
    pub sequence: u64,
}
```

Note: `StoredAuditEvent` does NOT store the Merkle inclusion proof or
the root. It throws away everything that makes the audit crate
*interesting* (the Merkle commitment, the proofs) and keeps only the
flat event tuple. So the one bridge that exists deliberately discards
the privacy-preserving and tamper-evident properties that motivate the
audit crate's existence. If a node restart needs to reconstruct
proofs, it must re-feed every `StoredAuditEvent` back into a fresh
`AuditLog::append` (which works because event hashing is canonical)
and rebuild the tree.

Nothing else consumes any output the audit crate produces. The proofs
themselves (`CountProof`, `RangeProof`, `ConsistencyProof`,
`BudgetProof`, `LastUseProof`) are never sent over a wire format, never
verified by a remote party, never embedded in a receipt, never serialised
to a file in any production code path. They exist; they verify in
their own unit tests; nothing else cares.

**This is a strong delete signal.**

---

## §4 — Historical context: in-progress sketch or completed orphan?

Reading every file, the crate has the unambiguous shape of **finished
work that nobody picked up**, not the shape of an in-progress sketch.

### Signals it is finished

- **All `pub` types implement the standard derive cluster** — `Clone,
  Debug, PartialEq, Eq, Serialize, Deserialize` (or `Hash` where
  appropriate). No `// TODO`, no `unimplemented!()`, no `todo!()`, no
  `unreachable!()` with cleanup comments.
- **No `FIXME` / `XXX` / `HACK` comments anywhere in the crate.**
  Grepping `grep -rEn 'TODO|FIXME|XXX|HACK|unimplemented|todo!' audit/src`
  yields nothing.
- **Every proof type has a `.verify()` method with positive AND
  negative unit tests.** Tampering tests (`count_proof_fails_with_tampered_count`,
  `budget_proof_fails_bad_arithmetic`, `budget_proof_fails_count_mismatch`,
  `range_proof_fails_outside_range`) exercise the adversarial path.
- **`tests.rs` reads as a finished demo script**: `end_to_end_budget_enforcement`,
  `end_to_end_consistency_proof`, `end_to_end_range_proof`,
  `end_to_end_multi_token`, `non_repudiation`, `interleaved_tokens`,
  `windowed_budget_proof_across_windows`, `stress_many_events`, etc.
  Every story the doc-comment promises has a corresponding test.
- **Optimization work has been done.** `AuditLog` was clearly written
  twice: once naively (`compute_root_from_scratch`, kept only under
  `#[cfg(test)]` to validate the cached version) and then with
  incremental cached `tree_levels`. The cached path is the production
  path; the naive path stays around purely as an oracle in
  `rebuild_tree_and_verify`. This is the shape of *post-optimisation
  polish*, not the shape of a half-built feature.
- **Historical-roots pruning** is parameterised
  (`DEFAULT_HISTORICAL_ROOTS_LIMIT = 10_000`, `with_roots_limit`,
  `set_historical_roots_limit`) — somebody thought about long-running
  systems. That kind of detail rarely appears in a sketch.
- **Domain-separation tags** are namespaced (`"pyana-audit event v1"`,
  `"pyana-audit index-commit v1"`) — somebody was thinking about future
  schema evolution.
- **Doc comments are full prose**, including the ASCII-art architecture
  diagram in `lib.rs` and the runnable doctest example. This is
  documentation-as-handoff, not as scaffolding.

### Signals it might still be in-progress

- `ConsistencyProof::verify_structure` is explicitly *structural*:
  > Full verification requires reconstructing the old root from the
  > new tree's prefix, which requires the actual leaf data. This method
  > verifies the structural properties.
  So a *complete* consistency-proof verifier (one that hashes bridges
  back into a root) does not exist. The doc comment acknowledges the
  gap but doesn't close it. This is the only place I'd call the crate
  unfinished — and even there, it's a documented limitation, not a
  hidden bug.
- `prove_range` returns *every* event for the token and lets the
  verifier check the range — i.e., it's not a true zero-knowledge range
  proof, it's a "here are all the timestamps, you check they fit"
  proof. The privacy story is weaker than the doc claims. Specifically,
  for a token with K uses, the auditor learns K timestamps, which is
  more information than "all K uses fall in [t1, t2]".
- The `CountProof` similarly leaks the *set of indices* (committed but
  derivable from the inclusion-proof leaves). The auditor can't see
  `action_hash` or `verifier_id`, but the auditor *can* see which
  positions in the log were token-X events. That's not nothing.

So the privacy-preservation claim is somewhat oversold by the
doc-comment, but the code does what the *implementation comments* say
it does. The crate is best characterised as *complete relative to its
own design, but with a design that doesn't quite live up to its
marketing*.

### Git history

```
a8a4660a checkpoint
926f90ef comprehensive polish: DoS limits, linear fallback removed, valid_after enforced, licenses, tracing, panics→errors, dead code, version standardization
814ca85f massive integration pass: dual-hash bridge, node↔extension, EventualRef fires, SDK real proofs, budget→executor, AttestedRoot unified, deps cleaned, policy fixed
1032644a infra docs, discovery in extension, cleanup stale review files
8cc3c2b4 pyana: distributed object-capability authorization with ZK proofs
```

Five commits touching `audit/`. The most recent (`a8a4660a checkpoint`)
is a generic checkpoint, not a feature commit. `814ca85f` is the
"budget→executor" integration pass — but that turned out to be about
the `coord::budget` and the executor's `ComputronCosts`, not about
plumbing `audit::*` into the executor. The audit crate has not been
meaningfully touched since the integration pass that *bypassed it*.

This crate was finished, set on a shelf, and the team built around it.

---

## §5 — Conceptual overlap with the rest of pyana

The audit crate's stated goal — "verifiable token usage history without
revealing the full history" — overlaps with at least four other
subsystems. In each case the existing subsystem either subsumes the
audit crate's role or covers a different surface that the audit crate
does not.

### 5a. `observability/` (pyana-observability)

`observability/src/events.rs` defines `TraceEvent` with variants
including `Authorization`, `SovereignWitness`, `StateConstraint`,
`BilateralReceipt`, `Federation`, `TurnLifecycle`. Every authorization
(including `Bearer`, `Proof`, `Breadstuff`, `Signature`,
`CapTpDelivered`, `Unchecked`) emits a structured trace event with:

- envelope: schema version, monotonic seq, ISO-8601 timestamp, optional
  `turn_hash`, `actor`, `federation_id`, `cell_id`;
- payload: variant body with cert/proof hashes, *not* private material.

This is the live mechanism for "every time a token gets used, record
it." It is consumed by Studio for replay. It does NOT produce a
Merkle root; it does NOT support inclusion proofs to third parties.

**Overlap with `audit/`:** Both record token usage. Observability
records *more* (every authorization variant, every constraint
evaluation), but provides *less* cryptographic structure (no Merkle
root, no inclusion proof, no third-party verifiable count). The
designs target different consumers — observability targets the cell
owner's Studio, audit targets a hostile third party.

### 5b. `trace/` (pyana-trace)

`trace/src/lib.rs` exposes `check`, `eval`, `policy`, `types`, `verify`
modules. This crate is the *policy / trace verification* layer:
runtime policy evaluation against an event trace, separate from the
emission layer in `observability/`. It does not record events; it
*judges* them.

**Overlap with `audit/`:** Essentially none — `trace/` is about policy
admissibility, `audit/` is about historical accounting. They could
compose (a trace policy that says "no more than 5 uses per hour" is
exactly what `BudgetEnforcer` enforces), but currently there is no
integration.

### 5c. Witnessed Receipt Chain (`turn/`, protocol-tests `receipt_chain`)

`WITNESSED-RECEIPT-CHAIN-DESIGN.md` exists at workspace root.
`turn::TurnReceipt`s form a hash-linked per-agent total order, verified
by `pyana_turn::verify::verify_receipt_chain`. The protocol-test
crate's `ReceiptChain` invariant (`protocol-tests/src/invariants/
receipt_chain.rs`) checks the chain is intact.

**Overlap with `audit/`:** Heavy. The receipt chain *already*
provides:

- An append-only ordered sequence per agent.
- Tamper-evident hash linking (`prev_hash` chaining).
- Verifiable globally without the verifier holding the whole chain
  (the per-agent receipt chain plus `verify_receipt_chain` is the
  consistency primitive).
- Non-repudiation: a receipt is signed and chained.

What it does NOT provide:
- A Merkle root (it's a linear hash chain).
- Inclusion proofs that are O(log N) to verify against a constant-sized
  root.
- Privacy-preserving counting (the auditor needs to see the chain to
  count).
- A natural place to attach a windowed-budget-status proof.

So the receipt chain *subsumes* the `LastUseProof` and
`ConsistencyProof` use cases (a receipt chain is structurally
append-only by construction) but does NOT subsume `CountProof` /
`BudgetProof` / `RangeProof` cleanly, because the chain is per-agent
not per-token. To get "token X was used K times" you'd have to scan
the agent's receipt chain and filter — which works in trusted-mode but
doesn't give you a third-party-verifiable summary.

### 5d. AIR proofs / SovereignCellWitness (`circuit/`, `turn/`)

The STARK + Plonky3 + Kimchi pipeline produces ZK proofs of cell
transitions. `SovereignCellWitness` (re-emitted as
`SovereignWitnessPayload` in observability) carries `(cell_id,
sequence, has_stark_proof)`. State constraints are enforced via AIR.

**Overlap with `audit/`:** Different layer. AIR proves "this cell
transition is admissible per its constraint." Audit proves "this token
was used K times against this verifier." The AIR layer cannot replace
the audit log: the cell-state transition proves *one* transition, not
the *cumulative history* of a token. Conversely, the audit log
doesn't know anything about cell state — it just sees
`(token_id, action_hash, verifier_id, timestamp, sequence)` opaque
tuples.

### 5e. `pyana_token::traits::BudgetSpec` (capability layer)

The token crate already declares budget policy as part of a macaroon
caveat. `AuthRequest` carries `budget_states: HashMap<String, u64>`
(populated by `coord::budget::budget_state_for_request`, per the doc
comment in `coord/src/budget.rs:319-336`).

**Overlap with `audit/`:** This is the *upstream* of what
`audit::budget` would enforce. The token says "limit = 5". The
verifier needs an enforcer to count uses. `audit::BudgetEnforcer` is
*one* implementation; `coord::BudgetCoordinator` is *another*
(distributed) implementation. The token layer doesn't pick one — it
just publishes the limit.

### Summary table

| Property `audit/` would enforce       | Already enforced by                                                                  | Gap?                                  |
|---------------------------------------|--------------------------------------------------------------------------------------|---------------------------------------|
| Append-only history of token use      | `turn::ReceiptChain` per agent + `observability::TraceEvent` per turn                | Audit gives Merkle root; chain is linear |
| Tamper evidence                       | `verify_receipt_chain` + signed receipts                                             | Audit gives O(log N) inclusion proofs |
| Third-party verifiable count          | Nothing currently                                                                    | **Real gap**                          |
| Third-party verifiable time range     | Nothing currently                                                                    | **Real gap**                          |
| Budget enforcement (single-writer)    | `coord::BudgetCoordinator` (distributed) and `pyana_token::traits::BudgetSpec` (declarative) | Audit's single-writer variant exists but unused |
| Privacy from auditor                  | `observability` already hashes proofs / strips cleartext per BOUNDARIES.md           | Audit's privacy story is partial (leaks index positions) |
| Append-only attestation               | Receipt chain                                                                        | No daylight                           |

**The real conceptual gaps that only `audit/` fills:**

1. Third-party-verifiable count / range / last-use proofs against a
   small commitment (32-byte Merkle root). Receipt chains can't do
   this without sending the whole chain.
2. A single-process, no-coordination budget enforcer with cryptographic
   non-repudiation of every debit.

Both of these are *real* but neither is *currently wanted* by any
consumer in the tree.

---

## Verdict

**MERGE** — Specifically: dissolve `audit/` and route its remains as
follows. **Do not delete outright, do not revive as-is.**

### Why not DELETE outright

The crate's `AuditLog` is the only Merkle-committed event log in the
tree. The privacy/proof primitives (`CountProof`, `RangeProof`,
`ConsistencyProof`) are real artefacts that the receipt chain cannot
produce. If we ever want a *third-party* verifiable "this agent used
this token K times in window W" attestation — for example, to feed an
external auditor, a bilateral counterparty, or a future bridge sink —
this crate is approximately the right shape for it. Throwing it away
forces re-implementation from scratch later. The code is well-tested,
documented, and depends only on `commit` + blake3 + serde, so its
maintenance cost is near-zero.

### Why not REVIVE as-is

It has zero in-tree consumers besides one optional storage bridge that
deliberately discards the cryptographic content. The privacy story is
oversold (positions leak, range proofs leak timestamps). The
"BudgetEnforcer" is a single-writer enforcer in a system that has
already chosen distributed enforcement (`coord::BudgetCoordinator`)
plus declarative policy (`pyana_token::traits::BudgetSpec`) plus
observability emission (`pyana_observability`). Reviving as a separate
crate produces a fourth budget abstraction nobody asked for.

### The MERGE plan

1. **Move `audit::{event, log, proofs}` into `commit/`** (or a new
   submodule `commit::merkle_log`). The 4-ary Merkle tree primitives
   already live in `pyana-commit`; the audit log is just a typed
   wrapper around them. The natural home for `AuditLog`,
   `InclusionProof`, `CountProof`, `RangeProof`, `LastUseProof`,
   `ConsistencyProof`, `BridgeHash`, `TimestampWitness`,
   `LogSnapshot`, `AuditReceipt` is alongside the Merkle primitives
   that already underpin them. Rename the public surface to
   `pyana_commit::merkle_log::*` and the proofs to
   `pyana_commit::merkle_log::proofs::*`. Drop the `audit-` prefix
   from domain-separation tags only if you bump the schema version;
   otherwise keep them.

2. **Delete `audit::budget`.** The `BudgetEnforcer` is a tiny wrapper
   over `(token_id, BudgetSpec, AuditLog)` with `record_use` doing
   `if can_use { log.append } else { Err(BudgetExhausted) }`. If
   anyone ever needs it, they can write this against the
   `pyana_commit::merkle_log` API in twenty lines. The `BudgetSpec`
   in audit duplicates `pyana_token::traits::BudgetSpec`; that
   duplication should also go.

3. **Update `store::audit`** to depend on
   `pyana_commit::merkle_log::UsageEvent` instead of
   `pyana_audit::UsageEvent`. The `store::audit::StoredAuditEvent`
   mirror remains as-is (it already throws away everything
   audit-crate-specific; it doesn't care about the upstream module
   path). Delete the `audit-bridge` feature gate and make it
   unconditional — the only reason it was gated was to avoid the
   `pyana-audit` dep, and once `pyana-audit` is gone there's nothing
   to gate.

4. **Fix `tests/src/budget.rs`** — its import is currently broken
   relative to `tests/Cargo.toml`. Update the imports to the new
   `pyana_commit::merkle_log` location and add the `pyana-commit` dep
   to `tests/Cargo.toml` (already a transitive dep but should be
   explicit if directly used). Or, if `tests/src/budget.rs` was
   accidentally left in place when something was removed, delete it.

5. **Remove `audit` from the workspace members list** in the root
   `Cargo.toml`. Remove the `audit/` directory.

6. **No salvage outside merkle_log.** The `BudgetEnforcer`,
   `BudgetExhausted`, `WindowInfo`, `BudgetSpec`, `BudgetProof` types
   should not be salvaged. `BudgetProof` is just `CountProof + arithmetic`
   and can be reconstructed in twenty lines by any caller that wants it.

### Estimated effort

- Code move: half-day (mechanical — five files, one rename per
  module).
- `store::audit` update: hour.
- `tests/src/budget.rs` repair: hour (decide salvage vs delete).
- Workspace + Cargo.toml cleanup: fifteen minutes.

Total: under a day. No semver concern (no external consumers).

### What this buys

- One place to look for "the Merkle-committed event log primitive"
  (already half there: `pyana-commit` owns the hash, `pyana-audit`
  owns the log; merging fixes that split).
- Removes the third "budget" namespace; leaves `coord::BudgetCoordinator`
  (operational) and `pyana_token::traits::BudgetSpec` (declarative)
  as the two budget abstractions, which is the correct count.
- Removes 2.5K LOC of dormant-looking workspace member, replacing it
  with ~1.5K LOC inside an already-load-bearing crate.
- Preserves the genuinely useful proof primitives for a future
  consumer (external auditor, bilateral counterparty, bridge sink)
  without making them a top-level concept.

### Pre-conditions for revival instead of merge

If any of the following lands before the merge happens, REVIVE
becomes the right call instead:

- A bridge or external auditor demands `CountProof`/`RangeProof` as a
  wire-format artefact.
- A token-broker app (`apps/*`) wires `BudgetEnforcer` into its
  verifier loop and emits `BudgetProof`s as part of receipts.
- The receipt chain grows a "summary attestation" hook that wants the
  `BudgetProof` shape for "K uses in window W."

In any of those cases, `audit/` becomes a load-bearing crate and
should stay as-is (after fixing the `tests/Cargo.toml` mismatch and
narrowing the privacy-claim doc-comment to match the implementation).

Absent any of those, the MERGE plan above is the right disposition.

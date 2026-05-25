# AUDIT-coord-crate.md — Deep audit of `pyana-coord`

> Read-only audit of the `coord/` workspace member.
> Generated 2026-05-24 against `main` @ commit `8a66164` (working tree
> has unrelated WIP edits to `circuit/`, `intent/`, `turn/`, `wire/`).
>
> Companion to `BACKWATER-CRATES-AUDIT.md`, which previously flagged
> `coord/` as "load-bearing but undocumented." This document discharges
> that flag.

Scope: every file in `coord/src/` (~6.9 KLOC implementation + 1.9 KLOC
tests in `tests.rs`), plus `Cargo.toml`, plus every consumer that
imports `pyana_coord::*` in the workspace. Reverse-dep search was
`grep -rn 'pyana_coord\|pyana-coord' --include='*.rs' --include='*.toml'`.

The crate's self-description (from `Cargo.toml`):

> Two-layer turn coordination: causal chaining + atomic multi-party turns

That tagline understates what is now in the crate. There are three
distinct mechanisms living in `coord/`, two of which are wired into
`node/` today and one of which is design-complete but uncalled by
production:

1. **Layer 1 — Causal chaining DAG.** Hash-pointer happened-before
   relationships between turns. Backed by `pyana_types::CausalDag`
   plus turn-aware wrappers (`CausalTurn`, `CausalLedger`).
2. **Layer 2 — Atomic multi-party 2PC.** Propose / Vote / Commit-or-
   Abort over a multi-participant call forest, with Ed25519 vote
   signatures, threshold QCs on commit, signed Abort messages, and
   coordinator/participant timeout recovery.
3. **Bounded counters — Stingray-style budget distribution.** Two
   variants: `BudgetCoordinator` (one agent's budget split across
   silos; 3f+1 BFT) and `SharedResourceBudget` (one shared resource
   split across agents; 2f+1 BFT, blocklace-derived, with Tier-2 →
   Tier-3 escalation state machine). A `FastUnlockManager` releases
   locks on 2PC abort.

The boundary between these three mechanisms is clean — they share
only `serde_sig` and `CoordError`. Layer 1 and Layer 2 communicate
implicitly (a committed atomic turn ends up in the causal DAG via the
node's normal receipt-append path), but `coord/` itself does not
glue them together; the node does. The bounded counters are not
referenced anywhere in `atomic.rs` or `causal.rs` — they are a third
module that happens to live in the same crate because the module
docstring on `budget.rs` says it "plugs into the Coordinator (atomic.rs)
as follows" (it does not, in code; the integration is done at the
node level).

---

## File-level breakdown

| File | LOC | Role |
|------|-----|------|
| `lib.rs` | 67 | Module wiring + re-exports + two-layer architecture doc |
| `atomic.rs` | 1113 | 2PC state machine: `AtomicForest`, `Coordinator`, `Participant`, `Vote`, signed messages |
| `budget.rs` | 1237 | Stingray bounded counter (`BudgetCoordinator`) + `FastUnlockManager` + `SpendingCertificate` + tests |
| `causal.rs` | 408 | Layer-1 `CausalTurn`, `CausalLedger`, `CausalTurnBuilder`; re-exports `pyana_types::CausalDag` |
| `error.rs` | 221 | `CoordError` enum + `From<TurnError>` / `From<LedgerError>` / `From<pyana_types::CausalError>` |
| `serde_sig.rs` | 25 | Serde adapter for `[u8; 64]` Ed25519 signature serialization |
| `shared_budget.rs` | 1897 | `SharedResourceBudget`, `SharedBudgetObserver`, debit payload encode/decode, Tier-2→Tier-3 state machine, blocklace integration, tests |
| `tests.rs` | 1897 | Integration tests for Layer 1 + Layer 2 (does not exercise `budget.rs` or `shared_budget.rs` — those have inline `#[cfg(test)] mod tests`) |

Cargo dependency graph (from `Cargo.toml`):

```
pyana-coord
├── pyana-cell   (CellId, Ledger, Preconditions)
├── pyana-blocklace (Block, Blocklace, Payload — used by shared_budget only)
├── pyana-turn   (Turn, TurnExecutor, TurnReceipt, CallForest, ComputronCosts)
├── pyana-types  (CausalDag re-export)
├── blake3
├── ed25519-dalek (Signer/Verifier/SigningKey/VerifyingKey)
└── serde
```

Importantly: **no `tokio`, no `tracing`, no `async`** anywhere in
`coord/`. The crate is synchronous and runtime-agnostic. The async
ceremony (HTTP handlers, gossip, locking) lives in `node/` and binds
each coordinator state machine inside a `tokio::sync::RwLock`.

---

## Per-module review

### `lib.rs`

The two-layer architecture is announced explicitly with an ASCII
diagram (see lib.rs lines 22–42). The diagram describes only Layer 1
and Layer 2; the bounded-counter modules are not mentioned in the
top-level docstring. That is the first surprise of the crate:
`lib.rs` declares itself as a two-layer turn coordination library,
but `pub mod budget` and `pub mod shared_budget` together are larger
than `atomic.rs` + `causal.rs` combined (3134 vs 1521 LOC), and they
implement an entirely different protocol family. **The crate has
grown into three concerns under a two-concern docstring.**

Re-exports: `atomic::*`, `budget::*` (renamed to drop module prefix
in callers' code), `causal::*`, `error::CoordError`, and
`shared_budget::*`. Every public type can be reached without naming
the submodule, which is convenient for callers but obscures the
three-protocol structure.

### `atomic.rs`

Where the meat is. Five top-level types:

- `AtomicForest` (lines 19–118). The bundle that a coordinator
  proposes to participants. Fields: `participants: Vec<[u8; 32]>`
  (node IDs), `forest: CallForest`, `preconditions: Vec<(CellId,
  Preconditions)>`, `initiator: CellId`, `fee: u64`, `hash: [u8; 32]`.
  Computes its identity hash over **participants × forest_hash ×
  full precondition contents × initiator × fee** under domain tag
  `b"pyana-coord:atomic-forest"`. A security comment on
  `compute_hash` (lines 60–87) calls out specifically that the full
  precondition contents are hashed (via `Preconditions::hash()`) to
  prevent hash collisions where two different precondition sets
  would produce identical forest hashes. The function `validate()`
  checks both `participants` and `forest` are nonempty;
  `estimated_cost()` lower-bounds the computron cost as
  `action_count * (action_base + effect_base)`.

- `Vote` (lines 122–248). `Yes { signature }` or `No { reason,
  signature }`. **Both Yes and No are signed.** The signing message
  is `proposal_id ‖ forest_hash ‖ vote_flag` where `VOTE_YES_FLAG =
  0x01` and `VOTE_NO_FLAG = 0x00`. Distinguishing Yes from No via
  the trailing flag byte ensures that one signature cannot be
  replayed as the other vote kind, even if the proposal-id and
  forest-hash are otherwise identical. The flag-byte trick is the
  same shape pattern used in BLS aggregation-aware schemes; here
  it's just Ed25519 with a domain-separated message.

- `Decision` (lines 252–261). `Commit | Abort | Pending`. Computed
  from current vote counts and the threshold via `evaluate_votes`.
  Pending if `yes_count < threshold` AND `no_count <= n -
  threshold`. Abort if too many No votes mean the threshold can
  never be reached: `no_count > n - threshold`. Commit if
  `yes_count >= threshold`.

- `Coordinator` (lines 343–786). State machine over
  `CoordinatorState::{Idle, Proposing, Committed, Aborted}`.
  `propose()` transitions Idle → Proposing; validates the forest,
  checks `0 < threshold <= participants.len()`, **gates on
  `estimated_cost <= max_budget`** (a per-proposal computron budget
  ceiling), assigns a `proposal_id = blake3("pyana-coord:proposal"
  ‖ forest_hash ‖ coordinator_node_id)`, and records the proposal's
  start `Instant` for timeout tracking. `receive_vote()` looks up
  the participant's registered Ed25519 pubkey in
  `participant_keys`, verifies the vote signature (rejecting with
  `InvalidVoteSignature` if it fails), refuses duplicate votes and
  votes from non-participants, and returns the new `Decision`.
  `commit()` extracts the forest+votes, double-checks
  `yes_count >= threshold` (defense-in-depth — the threshold should
  already have been verified by `evaluate_votes`), builds a single
  `Turn` from the forest with the initiator as the agent, executes
  it via `TurnExecutor::new(self.costs).execute(...)`, and emits a
  `CommitMessage` containing the `TurnReceipt` plus the (node_id,
  signature) pairs of the Yes voters. `abort()` signs an
  `AbortMessage` (signing message: `proposal_id ‖ ABORT_FLAG=0x02`)
  to prevent a network adversary from injecting fake aborts.
  `check_timeout()` is event-loop-driven: the caller passes in a
  `now: Instant`, and if `now - proposed_at >= proposal_timeout`,
  the coordinator self-aborts and returns the signed AbortMessage.

- `Participant` (lines 790–1039). The mirror role on each member
  node. Owns its `cell_id`, `node_id`, `signing_key`, a local
  `Ledger` view, `costs`, and a `vote_timeout`. After
  `evaluate_proposal()` votes Yes, the participant stamps
  `voted_yes_at = Some(Instant::now())` and `active_proposal =
  Some(proposal_id)`. If the coordinator crashes,
  `has_vote_timed_out()` detects expiry and `timeout_abort()` lets
  the participant unilaterally release its lock. The doc-comment on
  `Participant` (lines 790–798) explicitly addresses the abort-after-
  timeout safety argument: "safe because the coordinator cannot
  form a QC without continued lock from this participant." This is
  the right argument as long as participants do not double-vote
  after timeout. Nothing in this crate enforces non-double-voting
  across timeouts — it relies on the caller to drop the
  `Participant` after `timeout_abort()`.
  `evaluate_proposal()` checks: (a) we're listed as a participant,
  (b) forest validates structurally, (c) for any
  `(cell_id, preconditions)` entry that matches `self.cell_id`, we
  evaluate `cell_pre.evaluate(&cell.state)` against the local cell
  state. If all pass, signs Yes; otherwise signs No with reason.
  `apply_commit()` is the participant-side commit hook: it
  re-verifies the QC (`signatures.len() >= threshold`,
  **every signature in the QC is checked individually** against the
  expected pubkey + proposal_id + forest_hash), rebuilds the same
  `Turn` the coordinator built, and executes it locally.

- `AtomicForestBuilder` (lines 1043–1113). Conventional builder.
  Note: `build()` returns `Err(NoParticipants)` if no initiator is
  set — slight naming mismatch; one would expect `MissingInitiator`,
  but the existing `CoordError` enum has no such variant. Minor
  cleanliness issue.

Notable design choices:

- **Precondition hashing.** A pre-existing security comment notes
  that earlier versions hashed only the precondition COUNT or a
  shallow summary, which would have allowed collision attacks
  where two semantically different proposals had the same forest
  hash. Current code hashes `Preconditions::hash()` (defined in
  `cell/src/preconditions.rs`), which canonical-hashes the
  precondition contents. This is the right fix and the comment
  documents the lesson.

- **Coordinator signing key is per-node, not per-proposal.** The
  coordinator's signature on `AbortMessage` covers only
  `proposal_id ‖ ABORT_FLAG`. There is no binding from the abort
  signature to the original ProposeMessage author other than the
  proposal_id, which already includes the coordinator's node_id in
  its hash. That's adequate as long as proposal_ids are not
  predictable — and they aren't, since the forest hash includes the
  full forest and preconditions.

- **`commit()` builds a Turn with empty `depends_on` and
  `previous_receipt_hash: None`.** This is a load-bearing design
  decision: the atomic turn is its own causal entry, not chained
  off any prior receipt of the coordinator. The integration with
  Layer 1 (causal chaining) happens at the node level when the
  receipt is appended to the causal DAG, not inside `commit()`.
  See `causal.rs::apply_pipeline` for how pipeline-derived turns
  get causal_deps from the current frontier.

- **`max_budget` gating happens at propose-time only.** Once a
  proposal passes the budget gate, the executor metering still
  applies during `commit()`. There is no separate budget gate
  between vote-collection and commit; the assumption is that the
  estimated cost is a lower bound, and any blow-up will be caught
  by the TurnExecutor's own metering during `commit()`. That's
  consistent with how the executor handles `TurnResult::Rejected`
  (mapped to `CoordError::TurnExecution`).

Surprises:

- The `commit()` and `apply_commit()` paths each build the `Turn`
  independently from `forest.initiator + agent_cell.state.nonce()`.
  Both sides must observe the same nonce. If the participant's
  local ledger has the initiator at a different nonce than the
  coordinator's view (e.g., because the participant's view is
  behind), the executor will reject. This is a real divergence
  surface, not documented in the doc-comments. **A clean
  improvement would be to ship the nonce as part of the
  ProposeMessage and have both sides use that.**

- `agent_cell.state.nonce()` is called in `commit()` without
  incrementing it. The executor is responsible for nonce-bumping
  via `Effect::IncrementNonce` or implicitly via the turn-execution
  contract. (See `turn/src/executor.rs` for the actual nonce
  bookkeeping.) This is *not* a bug — it's just that the
  `Turn.nonce` field is the *expected* nonce at the time of
  execution, not the new nonce.

Open TODOs in atomic.rs: none visible.

### `budget.rs`

The "Stingray" module. Comment at lines 1–46 cites the design
lineage as `arXiv:2501.06531`. The module heading is the *only*
mention of "Stingray" in the public API surface — the type names
are deliberately generic (`BudgetCoordinator`, `BudgetSlice`,
`SpendingCertificate`, `FastUnlockManager`), with the lineage
hidden in module docs. See §2 below for what the Stingray paper
actually is and how the implementation maps to it.

Top-level types:

- `BudgetSlice` (lines 75–166). Per-silo slice state: `(agent,
  version, ceiling, spent, debits: Vec<DebitDigest>)`. The
  `try_debit(amount, digest)` method gates on `amount <=
  remaining()`. The `certificate(silo, signing_key)` method emits
  a `SpendingCertificate` signed over `agent ‖ version ‖ spent ‖
  silo`. `refund(amount)` decrements spent — used by FastUnlock on
  abort.

- `SpendingCertificate` (lines 173–190). The silo's attestation:
  `(silo, agent, version, total_spent, debits, signature: [u8; 64])`.
  The signature is meant to be verified during rebalancing — but
  see "Surprises" below: **`rebalance()` does NOT verify
  certificate signatures**.

- `BudgetCoordinator` (lines 193–451). Manages slice distribution
  across silos for one agent. `new(agent, total_balance, silos,
  byzantine_tolerance)` rejects unless `n >= 3f+1`. The slice
  ceiling math (lines 261–277):
  `ceiling = balance * (f+1) / (2f+1)`. The doc-comment is
  explicit that the sum of all slice ceilings *exceeds* the true
  balance by design — this is what enables coordination-free
  spending. The safety bound is that with at most `f` Byzantine
  silos, the maximum *undetectable* overspend is bounded by
  `f * ceiling`. `try_debit(silo, amount, digest)` is the hot
  path: O(1) HashMap lookup + slice.try_debit.

  `rebalance(&certificates)` (lines 357–450) requires ALL silos
  to submit certificates by default (`require_all_certs = true`);
  `rebalance_partial()` allows missing silos but assumes they spent
  their full ceiling. Both verify that certificates' agent/version
  match, that no silo submits twice, and that no certificate
  claims spending above its ceiling. **They do NOT verify the
  Ed25519 signature** on the certificate. There's even a comment
  in test `test_rebalance_rejects_overspend_certificate` at line
  1016: `// Forged signature (not verified in rebalance yet).`
  This is an open security gap: in the absence of signature
  verification, a malicious coordinator could forge certificates
  on behalf of a silo, claiming any spending up to the silo's
  ceiling. The ceiling check provides a safety floor but does not
  let honest silos refute fabricated certificates.

- `FastUnlockManager` (lines 511–686). Manages computron locks
  during 2PC. `lock(proposal_id, agent, amount, silo, version)`
  records a lock. `release_on_commit()` releases without refund
  (the resources were consumed). `vote_unlock(request, voter,
  has_signed_commit, signing_key)` produces an `UnlockVote`
  signed over `proposal_id ‖ voter ‖ has_conflict_byte`.
  `apply_unlock_certificate(cert)` verifies the certificate has
  `>= 2f+1` votes with NO conflicts, then releases the lock,
  returning `(amount, silo)`. `apply_unlock_and_refund(cert,
  coordinator)` additionally refunds the silo's slice.
  Note: `apply_unlock_certificate` **does NOT verify the
  Ed25519 signatures on the votes** — same gap as `rebalance`.
  The vote-count check protects against insufficient quorum but
  not against forged votes.

- Convenience alias: `pub type ComputronBudget =
  BudgetCoordinator;`. Lets callers spell out their intent
  without the engine knowing about computrons specifically.

Tests in `budget.rs` (lines 794–1237): 13 tests, all in inline
`mod tests`. Coverage includes ceiling calculations for f=1 and
f=2, insufficient silo count rejection, concurrent debits,
exhaustion errors, rebalance happy path, incomplete-certificates
rejection, partial mode, wrong-version rejection,
over-ceiling-certificate rejection, lock/commit-release,
fast-unlock-after-abort, insufficient-vote rejection, blocked-by-
conflict, duplicate-lock, integration debit+abort+fastunlock+refund,
and Byzantine-overspend-is-bounded. The signature-verification gap
is not tested.

### `causal.rs`

Wraps `pyana_types::CausalDag` (re-exported) with turn-aware
machinery. Three types:

- `CausalTurn` (lines 41–95). A turn plus its causal metadata:
  `(turn, causal_deps: Vec<[u8; 32]>, node_id, sequence, hash)`.
  The hash binds all five components under domain tag
  `b"pyana-coord:causal-turn"`. `verify_hash()` recomputes and
  compares.

- `CausalLedger` (lines 99–377). A `Ledger` + `CausalDag` + per-
  node frontier tracking + per-node sequence tracking + receipt
  storage + executor config. `apply_causal_turn(ct)` does the
  full ingest:

  1. Recompute the hash and compare to the claimed hash
     (`HashMismatch` on failure).
  2. Check causal readiness (`MissingDependency` if any dep is
     not in the DAG).
  3. Check per-node sequence is monotone (`SequenceGap` if not).
  4. Insert into the DAG (`CausalCycle` / `DuplicateTurn` if not).
  5. Execute the turn via a fresh `TurnExecutor`.
  6. Update the per-node frontier (replace deps with this turn's
     hash + record sequence).
  7. Store the receipt if the turn committed.

  `apply_pipeline(pipeline, node_id)` bridges the pipeline-
  execution system to the causal DAG: it executes the entire
  pipeline, then for each committed turn wraps the turn in a
  CausalTurn with appropriate causal_deps (base frontier + intra-
  pipeline deps), inserts into the DAG, and records receipts.

- `CausalTurnBuilder` (lines 379–408). Helper for constructing
  CausalTurns from the current ledger state — fills in
  `causal_deps` from `ledger.frontier()` and `sequence` from
  `ledger.next_sequence(node_id)`.

The `From<pyana_types::CausalError>` conversion (lines 23–35)
maps `MissingDeps { turn_hash, missing }` to
`CoordError::MissingDependency { turn_hash, dep_hash: missing[0] }`
— it drops all but the first missing dependency. That's lossy: a
turn with three missing deps will surface only the first when
displayed. This is documented nowhere and is a minor wart.

TODOs (lines 367–371):
- `TODO(#13)`: concurrent turn conflict detection tests.
- `TODO(#14)`: recovery-after-crash tests (partial DAG replay).
- `TODO(#15)`: documentation for cross-layer interaction between
  causal ordering and the 2PC protocol.

The TODO #15 is the missing piece this audit document partially
addresses. See §1 below.

### `error.rs`

`CoordError` is a single flat enum with 17 variants. The variants
are partitioned by comment headers into "Layer 1 errors", "Layer
2 errors", and "Underlying errors". Notable: there's no dedicated
variant for budget errors — `BudgetError` (defined in `budget.rs`)
and `SharedBudgetError` (defined in `shared_budget.rs`) are
separate types, and there's no `From<BudgetError> for CoordError`
or similar. **This means consumers handle budget errors via a
different code path than coord errors.** In `node/src/state.rs`,
`init_budget_coordinator` returns `Result<(), BudgetError>`
directly. The lack of a uniform error type is a small but real
cost of treating budgets as a third concern.

### `serde_sig.rs`

25 LOC. Serde adapter for `[u8; 64]` Ed25519 signature
serialization, since the stock serde derive only supports arrays
up to 32 elements. Used by `AbortMessage`, `SpendingCertificate`,
`UnlockVote`. Tested implicitly via the postcard/serde round-trip
in higher-level tests.

### `shared_budget.rs`

The newest module in the crate (1.9 KLOC, ~280 LOC of design
commentary in the module head). Generalizes the bounded counter
from "one agent's budget split across silos" to "one shared
resource split across agents." Key changes vs `budget.rs`:

- **BFT threshold is 2f+1** (not 3f+1), because participants ARE
  the agents (not replicated nodes). Need a quorum of honest
  participants to attest to spending.
- **Allowances are derived from the blocklace** rather than
  reported via signed certificates. `sync_from_blocklace`,
  `sync_from_blocklace_blocks`, and `sync_from_debit_map` let the
  coordinator compute per-agent spending by reading each agent's
  virtual chain.
- **Adds an escalation state machine.** `ResourceState::{Open,
  Closing { conflicting }, Rebalancing}` with transitions:
  Open → Closing (overspend detected) → Rebalancing (tau orders
  conflicting blocks) → Open (resolution applied). `resolve_with_ordering`
  processes debits in tau order, accepting them until balance is
  exhausted; later debits get `DebitResolution::Rejected`.
- **Adds credits** (deposits during an epoch increase the
  resource balance immediately, not just at rebalance).
- **Wire format for debits in blocks.** `encode_debit_payload`
  prefixes a `0x44` tag byte, then the 32-byte resource_id, then
  the 8-byte LE amount. `extract_debit_for_resource` and
  `extract_resource_debit` decode the same format. The 41-byte
  payload is embedded inside a `pyana_blocklace::Payload::Turn`
  or `::Data`.

Additional types:

- `AgentAllowance` — per-agent state, mirrors `BudgetSlice` but
  with `resource: ResourceId` instead of an implicit silo. Has
  `refund()`, `try_debit()`, `remaining()`.
- `SharedBudgetObserver` — manages multiple `SharedResourceBudget`s
  keyed by `resource_id: [u8; 32]`. `on_blocklace_update(&[&Block])`
  is the on-new-blocks hook: for each block, decode the resource
  debit (if any), record it, and escalate the budget if the new
  observation pushes total spending past the balance. Returns the
  list of resources that just entered escalation.

`try_optimistic_debit(agent, amount, digest) -> bool` (lines 466–
482) is the Tier-2 fast path: returns true if the debit was
accepted within allowance (consensus-free), false if the resource
is in Closing/Rebalancing or the agent's allowance is exhausted.
On exhaustion, **automatically escalates** the resource by
calling `self.escalate(Vec::new())`. The empty conflicting set is
notable — the caller is expected to populate it later when they
have a blocklace scan. This is a slight wart: the type system
does not enforce that `escalate` was eventually called with the
actual conflicting block IDs.

Tests in `shared_budget.rs` (lines 925–1897): 29 tests covering
ceiling math, concurrent debits, exhaustion, AMM-pool overspend
scenario, no-overspend with conservative agents, rebalance happy
path, rebalance with partial reports, rebalance with wrong
ceiling, credits, dynamic add/remove participant,
`sync_from_debit_map`, fast-path-eliminates-lock-round (which is
just a doc test rather than a real comparison), Byzantine-
overspend-is-bounded, full epoch lifecycle, escalation blocks new
debits, `would_overspend`, full state-machine round-trip,
encode/decode debit payload, solo-mode (n=1, f=0), 3-agent
overspend scenario, tau-resolution accepts/rejects, sync_from_
blocklace_blocks derives state, sync_from_blocklace_blocks
triggers escalation, sync_from_blocklace_blocks ignores wrong
resource, try_optimistic_debit accepts within allowance,
try_optimistic_debit escalates on exceed, try_optimistic_debit
rejects when closing, try_optimistic_debit resumes after
resolution, full escalation round-trip.

Test mass roughly matches implementation mass. Coverage looks
real, not nominal.

### `tests.rs`

1.9 KLOC of integration tests that exercise the Layer-1 and
Layer-2 paths together. Imports both `atomic::*` and `causal::*`.
Does NOT touch `budget.rs` or `shared_budget.rs` — those have
their own inline test modules. The split is reasonable
(`tests.rs` is for cross-module integration tests; budget/
shared_budget are self-contained).

Specific test categories (read from the `mod` headers):

- `mod causal_dag` — DAG construction, sequence validation,
  frontier tracking.
- 2PC tests (no top-level `mod` — flat at file scope after
  causal): propose/vote/commit, propose/vote/abort, threshold
  policies, signature verification (Yes and No), duplicate vote
  rejection, unknown participant rejection, signature replay
  rejection across proposals, signed abort messages, vote
  timeout, coordinator timeout, end-to-end multi-participant
  flow.

---

## Integration status (who calls coord)

Exhaustive list of consumers, by source file:

### `node/`
- `node/Cargo.toml:23` — declares dep.
- `node/src/state.rs` — uses `Coordinator`, `AtomicForest`,
  `BudgetCoordinator`, `BudgetError`, `FastUnlockManager`,
  `SiloId`, `SpendingCertificate`, `UnlockCertificate`,
  `UnlockRequest`, `UnlockVote`. The `NodeStateInner` struct
  holds `budget_coordinators: HashMap<CellId, BudgetCoordinator>`,
  `fast_unlock_manager: Option<FastUnlockManager>`,
  `silo_id: SiloId`, `pending_spending_certificates:
  Vec<SpendingCertificate>`, `pending_unlock_requests:
  Vec<UnlockRequest>`, `budget_epoch: u64`,
  `atomic_proposals: HashMap<[u8; 32], ActiveProposal>`. See
  state.rs lines 159–186.
  Methods: `init_budget_coordinator` (line 715),
  `try_budget_debit` (line 746),
  `collect_spending_certificates` (line 764),
  `rebalance_budgets` (line 786),
  `create_unlock_request` (line 827),
  `vote_on_unlock` (line 845),
  `apply_unlock_certificate` (line 856),
  `expire_stale_proposals` (referenced from api.rs:2358; defined
  earlier in state.rs).
- `node/src/api.rs` — the HTTP/REST handlers for the 2PC
  protocol:
  - `POST /turn/atomic` (api.rs:2311, `post_atomic_proposal`):
    builds `AtomicForest`, creates `Coordinator::new` with
    `MAX_ATOMIC_BUDGET = 1_000_000_000` (api.rs:513) as the cap,
    calls `propose()`, persists the coordinator in
    `s.atomic_proposals` keyed by proposal_id, optionally gossips
    the proposal to peers.
  - `POST /turn/atomic/vote` (api.rs:2465, `post_atomic_vote`):
    parses vote+signature, validates the signature pre-flight as
    defense-in-depth (lines 2492–2521) before passing to the
    coordinator, calls `coordinator.receive_vote()`, dispatches
    on `Decision::{Commit, Abort, Pending}`. On Commit, calls
    `coordinator.commit(&mut s.ledger)`. On Abort, calls
    `coordinator.abort("too many rejections — threshold
    unreachable")`.
  - `GET /turn/atomic/:id` (api.rs:2600, `get_proposal_status`):
    reads coordinator state and returns vote counts, age,
    threshold.
  - `POST /turn/atomic/evaluate` (api.rs:2654,
    `post_evaluate_proposal`): builds a `Participant` from the
    node's local identity and ledger, calls
    `participant.evaluate_proposal(&proposal_id, &atomic_forest)`,
    returns the signed Yes-or-No vote so the caller can submit
    it to the coordinator's `/vote` endpoint.

  Plus tests at api.rs:3942 that use `AtomicForest, Coordinator,
  Decision, Vote`.

### `wasm/`
- `wasm/Cargo.toml` — declares dep. No direct usage found in
  `wasm/src/` for `Coordinator` or `AtomicForest`; the dep may
  be transitive via re-exports or used in WASM-bound surface I
  didn't enumerate. (This is the same pattern as several other
  WASM-side crates: declared in Cargo, not visibly used in the
  Rust source.)

### `teasting/` (the workspace integration-tests crate)
- `teasting/Cargo.toml` — declares dep. Likely used to exercise
  end-to-end atomic-2PC scenarios.

### `demo-agent/`
- `demo-agent/Cargo.toml` — declares dep.
- `demo-agent/examples/unified_harness.rs:1085` — uses
  `BudgetCoordinator::new` in a demo (line 1091) with 4 silos,
  f=1, balance 1000.
- `demo-agent/examples/payment_channel.rs:11` — models a payment
  channel as a `BudgetCoordinator` (lines 129, 161).
- `demo-agent/examples/payment_channel_burst.rs:21` — uses
  `BudgetCoordinator` + `SpendingCertificate` to demonstrate
  bursty channel activity.
- `demo-agent/examples/multi_silo_budget.rs:12` — uses
  `BudgetCoordinator::new` (lines 63, 318).

### `turn/`
- `turn/src/budget_gate.rs` — declares its own local
  `BudgetSlice` struct that is *structurally identical* to
  `coord::budget::BudgetSlice` but lives in `turn/` to avoid a
  circular dep. The doc comment (lines 6–9) says: "The
  BudgetCoordinator in `pyana-coord` manages distribution and
  rebalancing at a higher level." This is one of those duplication-
  by-necessity layouts that comes from `coord` depending on
  `turn` already; in §3 below this audit explores whether the
  duplication is worth eliminating.

### `sdk/`
- `sdk/src/runtime.rs:196` — comment-only reference to
  `BudgetCoordinator` (in a doc comment explaining what runtime
  budget tracking *would* look like if integrated). Not an actual
  import.

### `preflight/`
- `preflight/src/checks/turns.rs:375` — comment-only reference to
  `SharedResourceBudget (BudgetGate)`. Not an actual import.

### `types/` and `net/`
- These crates each define their own `CausalDag` wrapper around
  `pyana_types::CausalDag`. They do NOT depend on `pyana-coord`.
  The Layer-1 type is shared via `pyana-types`, not via this
  crate. `coord/src/causal.rs` re-exports `pyana_types::CausalDag`
  for convenience.

**Summary of integration breadth:**
- `Coordinator`/`AtomicForest`/`Participant`/`Vote`: actively
  driven by node's HTTP API.
- `BudgetCoordinator`/`FastUnlockManager`: actively held in node
  state and exercised by per-agent budget initialization. **But:**
  there is no code in node that *calls* `try_budget_debit` from
  the executor hot path automatically — `state.rs` defines the
  method but I did not find a grep hit elsewhere in `node/` that
  invokes it on each turn. This is integration scaffolding that
  is plumbed but not yet load-bearing in production turn
  execution. The executor instead uses
  `turn/src/budget_gate.rs::BudgetSlice` (the duplicated type) as
  its gate. **The two budget systems are not currently
  connected: the executor-side gate is fed from its own slice
  state, not from `coord::BudgetCoordinator::silo_states`.**
- `SharedResourceBudget`/`SharedBudgetObserver`/Tier-2-3
  escalation: NOT used in production. Only demo-agent
  payment-channel examples. The `preflight/` mention is a
  comment in a docstring. **Aspirational scaffolding.**
- `CausalLedger`: NOT imported by node directly. `pyana_types::
  CausalDag` is imported by `net/` and `types/`, but
  `pyana_coord::CausalLedger` is not pulled into any non-test
  caller I could find. Demo-agent examples
  (`unified_harness.rs:37`, `causal_ordering.rs:11`) use
  `pyana_types::causal::CausalDag` directly, bypassing
  `coord::causal`. **The Layer-1 wrappers in `coord/` are
  effectively unused by production code.**

This is the most important finding of the audit. The crate's
self-description is "two-layer turn coordination," but in
practice:

- Layer 2 (atomic multi-party 2PC): **in production, driven by
  node HTTP API.**
- Layer 1 (causal chaining): **in production via
  `pyana_types::CausalDag` directly, not via this crate's
  wrappers.** `coord::CausalLedger`, `coord::CausalTurn`, and
  `coord::CausalTurnBuilder` are dead from the perspective of
  the node binary.
- Bounded counters: **plumbed in state.rs but not connected to
  the executor's actual budget gate.**
- Shared resource budget: **aspirational; demo-agent only.**

The crate is doing *less* useful work in production than its
docstring claims, and *more* work in `node/state.rs` is going
into the budget-coordinator state than is exercised by the hot
path.

---

## §1. 2PC protocol shape

The protocol coordinated by Layer 2 is a turn-level 2PC: a single
*call forest* (the combined actions of multiple agents on
multiple nodes) commits atomically across all participating
nodes, or aborts entirely.

### What is coordinated

An **`AtomicForest`** is the unit of coordination. It contains:

- A list of participating `node_id`s (one per node that must
  agree). These are the "voters."
- A `CallForest` (from `pyana-turn`) containing the actions
  contributed by all participants — flattened into one forest.
- A `Vec<(CellId, Preconditions)>` of per-cell preconditions that
  must hold on each participant's local ledger view.
- A single `initiator: CellId` who will be the `Turn.agent` when
  the forest is executed. This is the cell that pays the fee.
- A `fee: u64`.
- A self-hash of the above.

Critically: there is one and only one `Turn` constructed at
commit time, with `initiator` as its agent. The "multi-party"
nature lives in the forest's actions and in the precondition
list, not in the turn itself. From the executor's perspective,
this looks like a single agent's turn with a fat forest.

### Who initiates

The **coordinator** initiates. In production:

- The coordinator's `node_id` is the local node's `silo_id`
  (`state.rs:silo_id`, derived from the gossip pubkey).
- The coordinator's signing key is `state.wallet.
  gossip_signing_key()`.
- A client sends `POST /turn/atomic` with the forest, participant
  list, threshold, and (optionally) per-participant pubkeys.

### Who participates

Each `node_id` in the AtomicForest's `participants` list. Each
participant:

1. Receives the proposal (out of band — via gossip in the node's
   implementation, but the `coord` crate is transport-agnostic).
2. Builds a local `Participant` via `Participant::new`.
3. Calls `evaluate_proposal(&proposal_id, &forest)` which checks
   that the local ledger satisfies the participant's
   preconditions for its own cell.
4. Returns a signed `Vote::Yes` or `Vote::No`.
5. Submits the vote (in production via `POST /turn/atomic/vote`).
6. On `CommitMessage`, calls `apply_commit` to replay the turn
   locally.
7. On `AbortMessage`, optionally calls `verify_abort` to confirm
   the abort came from the legitimate coordinator (so that a
   network attacker can't cause spurious aborts).

### Commit / abort decision

The decision is computed by `evaluate_votes()` on the
coordinator side after every received vote:

- `yes_count >= threshold` → **Commit.** Coordinator calls
  `commit()` which executes the turn against its ledger,
  collects all Yes-vote signatures into a QC, and emits a
  `CommitMessage`.
- `no_count > n - threshold` → **Abort.** Threshold is now
  unreachable. Coordinator calls `abort(reason)`.
- otherwise → **Pending.** Wait for more votes.

Timeouts are handled outside the decision function:
`Coordinator::check_timeout(now)` returns a signed
`AbortMessage` if the proposal has been in `Proposing` state
longer than `proposal_timeout` (default 30s).
`Participant::has_vote_timed_out(now)` lets the participant
unilaterally release after `vote_timeout` (default 60s).

### Diagrammatic flow

```
        Coordinator                          Participants {A, B, C, ...}
        ───────────                          ─────────────────────────────
state: Idle

client POST /turn/atomic
  with forest, threshold, ...
        │
        ▼
   propose(forest)
        │ check participants nonempty, forest nonempty
        │ check 0 < threshold <= |participants|
        │ check estimated_cost <= max_budget
        │ assign proposal_id = blake3("pyana-coord:proposal"
        │                              ‖ forest_hash ‖ self.node_id)
        │ state = Proposing { forest, votes={}, proposed_at=Now() }
        ▼
  ProposeMessage { forest, coordinator, proposal_id }
        │
        ├──────► (gossip / RPC) ─────────────────► A, B, C
                                                   │
                                                   │  evaluate_proposal:
                                                   │    1. check listed
                                                   │    2. check forest.validate()
                                                   │    3. for each (cell_id, pre)
                                                   │       where cell_id == self.cell_id:
                                                   │         pre.evaluate(local_cell.state)
                                                   │    4. sign Yes:
                                                   │       sig = Ed25519(sk_X,
                                                   │            proposal_id‖forest_hash‖0x01)
                                                   │    OR sign No:
                                                   │       sig = Ed25519(sk_X,
                                                   │            proposal_id‖forest_hash‖0x00)
                                                   │
                                                   │  voted_yes_at = Now()
                                                   │  active_proposal = Some(proposal_id)
                                                   │
        ◄─────── Vote::Yes{sig} or Vote::No{reason,sig} ───── A
        ◄─────── Vote::Yes{sig} ────────────────────────── B
        ◄─────── Vote::No{reason,sig} ──────────────────── C
        │
        │ receive_vote(from=A, vote):
        │   verify participant in forest, not duplicate
        │   verify Ed25519(participant_keys[A], sig, msg)
        │   votes.insert(A, vote)
        │   decision = evaluate_votes()
        ▼
   decision?
        │
        │  Pending  → keep collecting
        │  Commit   → ┐
        │              │
        │  Abort    → ┤
        │              │
        ▼              ▼
   commit(ledger):                   abort(reason):
     verify yes_count >= threshold     sign abort:
     turn = Turn {                       sig = Ed25519(sk_C,
       agent: forest.initiator,                proposal_id‖0x02)
       nonce: ledger[initiator].state.nonce(), state = Aborted
       call_forest: forest.forest,       emit AbortMessage{
       fee: forest.fee, ... }              proposal_id, reason,
     executor.execute(&turn, ledger)       rejectors, signature }
     -> Committed { receipt }                        │
       OR Rejected { reason } → CoordError           │
                                                     │
     signatures = [(node_id, sig) for v in votes     │
                   if v == Yes]                      │
     state = Committed { receipt, proposal_id }      │
                                                     │
   CommitMessage {                                   │
     proposal_id, receipt, signatures }              │
        │                                            │
        ├──────► A, B, C ◄──────────────────────────┤
        │                                            │
        ▼                                            ▼
  Participant::apply_commit:                Participant: receive AbortMessage
    verify len(signatures) >= threshold       optionally verify_abort(sig,
    for each (node_id, sig) in signatures:                    coord_pubkey)
      verify Ed25519(participant_keys[id],     reset local state if voted Yes
                     proposal_id‖forest_hash‖0x01,
                     sig)
    rebuild same Turn from forest.initiator
    executor.execute(turn, local_ledger)
    -> receipt (matches coordinator's)

```

Notes:
- Vote messages are not themselves wrapped in an envelope by
  `coord`. The vote signature carries the binding to a specific
  proposal via the embedded `proposal_id`. The network layer is
  free to ship votes however it likes.
- Commit signatures form a "threshold QC" only in the sense
  that the participant verifies `len(signatures) >= threshold`
  in `apply_commit`. There is no BLS aggregation; signatures are
  raw Ed25519, one per Yes voter.
- The abort signature does *not* protect against an honest
  coordinator deciding to abort prematurely. It protects against
  a network adversary forging an abort message that did not come
  from the coordinator. Distinct attacker models.
- The `previous_receipt_hash` and `depends_on` fields of the
  built Turn are empty. The atomic turn is causally a "fresh
  start" from the executor's perspective. Layer 1's causal
  chaining happens later, when the receipt is written into the
  causal DAG by the node's append-path.

### What is NOT in 2PC

- **No locking phase.** The coordinator does not acquire locks
  on cells before proposing. Preconditions are evaluated
  optimistically at vote time. If a participant's local cell
  state changes between vote and commit, the commit's
  `executor.execute` will (re)check the precondition and may
  reject — at which point the coordinator catches
  `TurnResult::Rejected` and translates it to
  `CoordError::TurnExecution(reason)`. This is documented in
  `commit()` lines 605–637. The recovery is to call `abort()` —
  the api.rs handler does exactly this (lines 2553–2570).
- **No log / write-ahead state.** Coordinator state lives in
  `state.atomic_proposals: HashMap`. If the node crashes mid-
  protocol, all proposals are lost. The `created_at` field
  supports timeout-based GC (`expire_stale_proposals`,
  `PROPOSAL_EXPIRY_SECS = 120`) but there is no crash recovery.
  The 2PC is presumed to be tolerant of full-node restarts (the
  vote signatures and forest hash provide the only durable
  binding; in principle, a recovering node could re-fetch the
  proposal from gossip).
- **No view changes.** The coordinator is fixed for the lifetime
  of a proposal. If the coordinator goes silent, participants
  unilaterally abort via `has_vote_timed_out` after
  `vote_timeout` (default 60s). They do NOT elect a new
  coordinator. This is intentional and adequate as long as the
  protocol is restartable from the client (the originator can
  always issue a new `POST /turn/atomic`).

---

## §2. Stingray bounded counters

### What is Stingray

The module head of `coord/src/budget.rs` (lines 1–46) cites
`arXiv:2501.06531`. That paper is:

> Veera, Babel, Tas, Sonnino, Penna, Gola, Karame: *Stingray:
> Fast Concurrent Transactions Without Consensus* (Jan 2025).

Stingray is a system for executing concurrent transactions on
top of a partial-ordering substrate. The headline idea is the
**bounded counter**: a piece of distributed state that supports
concurrent local debits across multiple silos, with the
guarantee that the sum of debits will not overshoot a true
ledger balance by more than a bounded amount in the presence of
Byzantine silos. The bound is the so-called "Stingray
invariant":

```
slice_ceiling = balance * (f+1) / (2f+1)
```

with `f` the maximum Byzantine silos tolerated and `n >= 3f+1`
the total silo count. The sum of all silo ceilings is
intentionally larger than the true balance — this is what
enables coordination-free local debits — but the maximum
undetectable overshoot is bounded by `f * ceiling`. Honest
silos report their true spending at rebalance, and the protocol
deducts from the true balance to compute new ceilings.

The Stingray paper's contributions over prior work include:
- the bounded-counter primitive itself,
- a "fast unlock" mechanism for releasing locked resources
  after a 2PC abort without waiting for a full epoch timeout,
- and an analysis showing that this gives concurrent-
  transaction performance close to consensus-free latency for
  the common case where balances don't actually conflict.

### What the bounded counters enforce here

`BudgetCoordinator` (budget.rs:193–451) faithfully implements
the Stingray-style invariant:

- `compute_slice_ceiling` (lines 271–277) uses exactly the
  Stingray formula `balance * (f+1) / (2f+1)`, with u128
  intermediate arithmetic to avoid overflow.
- `BudgetCoordinator::new` enforces `n >= 3f+1`.
- `try_debit` is the local-only hot path: a single HashMap
  lookup + bounded-counter check + spent increment.
- `rebalance` (lines 357–450) is the periodic epoch close:
  collect certificates, sum, deduct from true balance,
  redistribute fresh slices.
- The doc comment on `compute_slice_ceiling` (lines 261–269)
  explicitly invokes the Stingray safety analysis: "with at
  most f Byzantine silos, the maximum overspend is bounded by
  f * ceiling."

`FastUnlockManager` (budget.rs:511–686) implements the second
Stingray contribution:

- `lock(proposal_id, agent, amount, silo, version)` records
  resources reserved by an in-flight 2PC.
- After 2PC abort, `vote_unlock` lets each silo sign a vote
  attesting whether it has a conflicting lock (i.e., whether it
  has already signed a commit for the same proposal — which
  would be a Byzantine action).
- `apply_unlock_certificate` requires `>= 2f+1` votes with no
  conflicts before releasing.
- `apply_unlock_and_refund` releases the lock AND credits the
  silo's slice back, which restores the bounded counter to its
  pre-debit state.

### Lineage gap (security)

The implementation faithfully reproduces the Stingray math, but
two pieces of the Stingray protocol are NOT enforced by code:

1. **Certificate signature verification.** `SpendingCertificate`
   carries an Ed25519 signature, and `BudgetSlice::certificate`
   correctly signs over `agent ‖ version ‖ spent ‖ silo`. But
   `BudgetCoordinator::rebalance_inner` (lines 370–450) does not
   verify the signature when consuming certificates. Test
   `test_rebalance_rejects_overspend_certificate` at line 1016
   even has a comment confessing "Forged signature (not verified
   in rebalance yet)." This is the most concrete security gap in
   the crate.

2. **Unlock vote signature verification.**
   `FastUnlockManager::apply_unlock_certificate` (lines 619–
   655) checks vote count and conflict flags but does not
   verify the Ed25519 signature on each `UnlockVote`. A
   Byzantine coordinator could fabricate votes.

Both are silent-overspend / silent-unlock attack surfaces under
the Stingray adversary model. Neither is exercised by tests.
**This audit recommends adding signature verification to both
paths and adding adversarial tests that confirm rejected
certificates / votes are observable to the caller.**

### `SharedResourceBudget` lineage

`shared_budget.rs` extends the Stingray primitive to the
"shared resource" case (one balance, n participants). The math
is identical but the BFT threshold drops to 2f+1 because the
participants ARE the agents, not replicated nodes. The module
doc (lines 1–71) explains the relationship to the COD ("Close-
Open-Debit") pattern from Astro and other prior work, framing
the shared budget as a **hybrid pre-allocative + reactive**
design:

- **Pre-allocative**: assign allowances upfront; debits are
  local + O(1).
- **Reactive**: when `is_overspent()` returns true, escalate to
  Tier 3 ordering for tau-based conflict resolution.

This module is the only place in the crate that depends on
`pyana_blocklace`. The wire format (`encode_debit_payload`,
lines 822–831) is described in the docstring as "a simplified
wire format; production would use postcard or a more structured
encoding" — so the payload encoding is a deliberate
simplification, flagged as such.

### Citation suggestion

`budget.rs` cites `arXiv:2501.06531` but does not name the
paper or authors. A one-line addition spelling out the title
and authorship would help future readers (and AUDIT-passes
like this one) without changing any code:

```
//! Stingray: Fast Concurrent Transactions Without Consensus
//! (Veera, Babel, Tas, Sonnino, Penna, Gola, Karame, 2025).
//! arXiv:2501.06531
```

---

## §3. `coord::budget` vs `audit::budget`

The `BACKWATER-CRATES-AUDIT.md` flagged this as a duplicate.
After reading both files, the truth is: **they are not
duplicates, but they should converge.**

### What `coord::budget` does

`coord::budget::BudgetCoordinator` is the **distributed
spending throttle**:

- Subject: an agent's spendable resource (computrons / API
  calls / storage / tokens).
- Domain: multiple silos (replicated nodes) executing on
  behalf of the same agent.
- Invariant: bounded-counter; sum-of-spending within true
  balance modulo `f * ceiling` Byzantine overshoot.
- Authority: derived from the silo set + 3f+1 quorum at
  rebalance. (Plus per-silo signed certificates — though see §2
  for the unverified-signature gap.)
- Proof artifact: `SpendingCertificate` (signed).
- Use case: every turn that consumes computrons goes through a
  `try_debit` of the agent's slice.

### What `audit::budget` does

`audit::budget::BudgetEnforcer` is the **per-token usage
counter** with privacy-preserving proofs:

- Subject: one token's usage count (or windowed usage count).
- Domain: a single audit log, not distributed.
- Invariant: `uses_consumed < budget_limit` (and within
  window if windowed).
- Authority: the local audit log Merkle root.
- Proof artifact: `BudgetProof` (an inclusion-style proof
  against the audit log's 4-ary Merkle tree).
- Use case: every token presentation increments a counter and
  proves the increment is within the spec.

### How they differ

| Dimension | `coord::budget` | `audit::budget` |
|-----------|-----------------|------------------|
| What counts | A resource amount (u64) | A use count (u64) |
| Who counts | Per-silo bounded counter | Per-token usage log |
| Replication | Distributed (n silos) | Local (one log) |
| Rebalance | Yes, on epoch boundary | No |
| Time windows | No | Yes (windowed spec) |
| Byzantine bound | Stingray f*ceiling | N/A (local trust) |
| Proof | SpendingCertificate (signature) | BudgetProof (Merkle path) |
| ZK-friendly | No | Yes (log root commits) |
| Consumers | node state (BudgetCoordinator) | store (audit-bridge), tests |
| Live in production | Plumbed but not executor-driven | Not connected to any executor path |

These do not duplicate each other; they answer different
questions. **`coord::budget` answers "may this silo locally
spend X without coordinating?", while `audit::budget` answers
"has this specific token been used more than its allowed N
times, and can I prove it?"**

A token-presentation event is naturally both — it is one *use*
of the token (which `audit::budget` would count) and it is a
debit of the agent's compute budget (which `coord::budget`
would track). The right architecture is for both to fire on
the same event; the wrong architecture is to fold them into a
single type.

### Recommendation

**Keep both, but fix the integration story.** Specifically:

1. `coord::budget::BudgetCoordinator` should survive. It is the
   distributed primitive and the only one that runs in node
   state today.

2. `audit::budget::BudgetEnforcer` should also survive, BUT
   should be wired into the token-presentation path. Today no
   code calls `BudgetEnforcer::record_use` outside tests. The
   natural wiring is at the `bridge::present`
   path-of-execution: every successful presentation issues a
   `UsageEvent`, which is appended via `BudgetEnforcer`. See
   `AUDIT-bridge.md` (not yet written) or the recommendation
   in `BACKWATER-CRATES-AUDIT.md` `audit/` entry.

3. Rename one of them so the duplication-by-name doesn't
   continue confusing readers. The cleanest rename is to call
   the coord type `pyana_coord::budget::StingrayCounter` (or
   `pyana_coord::budget::BoundedCounterCoordinator`), keeping
   `BudgetEnforcer` as the per-token name. This makes the
   distinct semantics impossible to confuse.

4. Add a top-level `BUDGETS.md` or similar that names both and
   states the boundary between them. (Designer-decision; not
   part of this audit's prescribed surface.)

---

## §4. Composition with the rest of pyana

Searching for where `pyana_coord` types appear in other crates'
public surfaces:

- **`turn/`** — `turn::budget_gate::BudgetSlice` duplicates
  `coord::budget::BudgetSlice` to break what would otherwise be
  a circular dep (`coord` already depends on `turn`). The
  duplicated type is the *executor-side* gate; the canonical
  type is the *coordinator-side* gate. Both are needed because
  the executor cannot know how to rebalance and the coordinator
  cannot know how to execute. **Composition direction: turn ←
  coord.** The duplication is structural, not accidental.

- **`blocklace/`** — Used by `coord::shared_budget` only. The
  composition direction is `coord::shared_budget → blocklace`:
  the shared-budget module reads the blocklace as the ground
  truth for per-agent debits. Blocklace itself does NOT know
  about budgets; it just stores blocks.

- **`federation/`** — No direct dep. Federation does not import
  `pyana_coord`. The atomic-2PC protocol does not interact with
  federation membership rotation; the participant pubkeys are
  passed in from outside.

  However, note that in `node/src/api.rs` the participant
  pubkey resolution falls back to `s.known_federation_keys`
  (api.rs:2387–2406), so in practice the federation key set IS
  the set of admissible coordinator/participant identities.
  The binding is implicit and lives in node code.

- **`captp/`** — No direct dep. CapTP's session-establishment
  layer is below `coord/` in the stack. The 2PC protocol's
  vote-and-commit messages would be carried over CapTP sessions
  in production but `coord` has no CapTP-aware code.

- **`intent/`** — No direct dep. Intents are matched and
  cleared by a separate path (the trustless intent engine, see
  `intent/src/trustless.rs`). The atomic-2PC protocol could in
  principle be used to settle a matched intent atomically
  across participating agents, but no code wires this today.
  **This is the strongest aspirational integration story I see
  for the crate.** If intent settlement moves to an atomic-2PC
  commit, the crate's Layer 2 immediately becomes load-bearing
  for the intent system rather than for raw multi-party turns.

- **`cell/`** — Used as a type dependency: `CellId`,
  `Preconditions`, `Ledger`. Composition direction: `coord →
  cell`.

- **`types/`** — `CausalDag` is re-exported. The Layer-1 DAG
  type lives there. Composition direction: `coord → types`.

### Where coord types appear in others' APIs

- `node::ActiveProposal { coordinator: Coordinator, created_at:
  Instant, forest: AtomicForest }` (state.rs:270–277).
  The `coordinator` field is **the strongest leak of
  `coord::Coordinator` into another crate's public surface**.
  Anyone reading the node API tracks the coordinator's state
  machine directly. This is fine — it's the right place for
  that.

- `node::NodeStateInner::budget_coordinators:
  HashMap<CellId, BudgetCoordinator>` (state.rs:163).
  Same comment — `BudgetCoordinator` leaks into node state by
  design.

- HTTP request/response types in `node::api`
  (e.g. `AtomicProposalRequest`) carry the forest, participants,
  threshold, etc., effectively re-exposing the shape of
  `AtomicForest` over the wire (in JSON). The fields are not
  literally `AtomicForest` (the request takes them
  unstructured) but the deserialisation in
  `post_evaluate_proposal` (api.rs:2668) parses a literal
  `pyana_coord::AtomicForest` from JSON. So `AtomicForest` is
  effectively part of the node's HTTP surface.

No other crate exposes coord types in its public API. The
"composition graph" is:

```
       sdk          intent          federation         bridge
                          \              \                 \
                           \              \                 \
demo-agent ──► node ──► coord ──► turn ──► cell
                          │
                          └────► blocklace (only shared_budget)
                          │
                          └────► types (CausalDag)
```

---

## §5. The "live in node" claim — concrete pointers

The BACKWATER audit said `coord/` is "multi-party 2PC + Stingray
bounded counters, live in node." The concrete code-pointers are:

### 2PC liveness in node

- `node/src/state.rs:186` — `atomic_proposals: HashMap<[u8; 32],
  ActiveProposal>` is part of the durable in-memory node state.
- `node/src/state.rs:270–277` — `ActiveProposal { coordinator:
  Coordinator, created_at: Instant, forest: AtomicForest }`
  wraps a coord-side state machine inside node-side metadata.
- `node/src/state.rs:`  — `expire_stale_proposals` GCs old
  proposals via `PROPOSAL_EXPIRY_SECS = 120`.
- `node/src/api.rs:912` — HTTP route `POST /turn/atomic`.
- `node/src/api.rs:2311–2458` — `post_atomic_proposal` handler;
  builds AtomicForest, creates Coordinator, calls propose.
- `node/src/api.rs:2465–2594` — `post_atomic_vote` handler;
  receives a signed vote, optionally verifies it pre-flight,
  feeds it to `coordinator.receive_vote`, dispatches on the
  resulting Decision.
- `node/src/api.rs:2600–2646` — `get_proposal_status`; reads
  CoordinatorState.
- `node/src/api.rs:2654–2696` — `post_evaluate_proposal`;
  Participant-side proposal evaluation handler.
- `node/src/api.rs:513` — `pub const MAX_ATOMIC_BUDGET: u64 =
  1_000_000_000;` is the budget cap fed to `Coordinator::new`.
- `node/src/api.rs:3942` — tests exercise `AtomicForest,
  Coordinator, Decision, Vote`.

### Budget coordinator liveness in node

- `node/src/state.rs:18–21` — imports `BudgetCoordinator,
  BudgetError, FastUnlockManager, SiloId, SpendingCertificate,
  UnlockCertificate, UnlockRequest, UnlockVote`.
- `node/src/state.rs:159–174` — node-state fields for budget:
  `budget_coordinators`, `fast_unlock_manager`, `silo_id`,
  `pending_spending_certificates`, `pending_unlock_requests`,
  `budget_epoch`.
- `node/src/state.rs:715–737` — `init_budget_coordinator(agent,
  total_balance, silos, byzantine_tolerance)`.
- `node/src/state.rs:746–758` — `try_budget_debit(agent, amount,
  digest)`.
- `node/src/state.rs:764–777` — `collect_spending_certificates`.
- `node/src/state.rs:786–822` — `rebalance_budgets`.
- `node/src/state.rs:827–839` — `create_unlock_request`.
- `node/src/state.rs:845–851` — `vote_on_unlock`.
- `node/src/state.rs:856–868` — `apply_unlock_certificate`.

### "Live" with a caveat

The BACKWATER claim is half right. The 2PC is genuinely live —
the HTTP endpoints work, and votes flow through `coord` code.
The budget coordinator is in node state and methods exist to
operate on it, **but I could not find a code path that
automatically debits the budget on a turn execution.** The
executor uses `turn::budget_gate::BudgetSlice` (the duplicated
type), and the connection back to `coord::BudgetCoordinator`
happens only when an external caller explicitly calls
`try_budget_debit`. Demo-agent examples do this; production
turn execution does not.

The honest characterisation: **2PC is hot, budget coordination
is scaffolded but cold.**

---

## §6. Privacy / boundary contract (per BOUNDARIES.md)

`BOUNDARIES.md` frames the privacy question as "who knows
what, by what primitive." Applied to `coord/`:

### Boundary §6.1 — 2PC participants vs outside

- **Inside the proposal:** the coordinator and all participants
  on the participant list. They see the full `AtomicForest`:
  every call, every effect, every cell affected, every
  precondition. They also see all votes and signatures.
- **Outside the proposal:** any node not on the participant
  list. They see, via gossip, the proposal-id and the
  metadata-only gossip message
  (api.rs:2438–2444: `{"type": "atomic_proposal",
  "proposal_id": <hex>}`). They do NOT see the forest, the
  votes, the abort reason, or the commit receipt unless they
  separately request `GET /turn/atomic/:id` (and that endpoint
  returns vote counts, not the votes themselves).
- **Enforcing primitive:** participant-list membership +
  application-layer routing of full proposals vs gossip
  digests. **There is no cryptographic enforcement** — a
  malicious participant could leak the forest. Privacy is
  *applicational*, not cryptographic.

### Boundary §6.2 — Vote authorship

- **Inside the binding:** the (proposal_id, forest_hash,
  vote_flag) ed25519 signature relation. Only the holder of
  participant X's signing key can produce a vote attributable
  to X.
- **Outside the binding:** anyone observing votes can verify
  authenticity but cannot forge.
- **Enforcing primitive:** Ed25519 sign/verify, with the
  domain-separated message containing both proposal_id and
  forest_hash to prevent replay across proposals.

### Boundary §6.3 — Abort authorship

Same shape as votes but with `ABORT_FLAG = 0x02`. The signature
binds an abort to a specific proposal_id and authorial
coordinator. This is the **fake-abort-injection** defence the
crate explicitly mentions in atomic.rs lines 297–299.

### Boundary §6.4 — Budget visibility

`BudgetCoordinator` holds the total balance and per-silo
spending in plaintext. Anyone with a reference to the
coordinator (in node, anyone who can read `state.write().await`
or `state.read().await`) sees everything. Slice state is
revealed at rebalance via `SpendingCertificate`s.
- **Inside:** the node operator (with state access) and
  rebalance participants.
- **Outside:** clients and gossip observers; they may see
  block-level debit payloads (via shared_budget's
  `encode_debit_payload`) but those are tagged-and-plaintext.
- **Enforcing primitive:** none. Budget state is *not*
  cryptographically hidden. (Compare with `audit::budget`
  which produces zero-knowledge-ish Merkle proofs of usage
  count — `audit::budget` has *some* privacy story, while
  `coord::budget` has none.)

### Boundary §6.5 — Causal-DAG visibility

`CausalLedger.dag` is public information. Causal predecessors
are not secret — they're hash links that any verifier needs.
This is consistent with `pyana_types::CausalDag`'s broader
design.

### Inconsistency to flag

`shared_budget`'s wire format (`encode_debit_payload`) writes
plaintext `(resource_id, amount)` into block payloads. If the
designer intends shared-resource debits to be private (e.g.
for an AMM with privacy-preserving swap sizes), this is the
wrong encoding. The current encoding is debug/test-grade. The
module docstring acknowledges this at lines 763–771.

### Recommendation

Add a `Boundary contract` doc-comment block at the top of
`coord/src/lib.rs` summarising:
- 2PC participant set bounds the visibility set (applicational).
- Vote and Abort authenticity is cryptographic.
- Budget state is fully public to silos.
- Shared-resource debits are currently in plaintext.

This makes the boundary explicit for future readers and
catches the "we thought it was private" mistakes early.

---

## §7. Open questions for designer

1. **Causal layer drift.** `coord::CausalLedger` /
   `coord::CausalTurn` / `coord::CausalTurnBuilder` are
   effectively unused in production; node, types, and net all
   reach for `pyana_types::CausalDag` directly. Was the
   intention for these wrappers to be the canonical caller
   surface, and the divergence is an oversight? Or are these
   wrappers vestigial from an earlier design, and should they
   be removed? Demo-agent examples use the wrappers, which is
   the only evidence they have a future.

2. **Budget coordinator is plumbed but not wired.** The
   executor uses `turn::budget_gate::BudgetSlice` (duplicated
   from `coord::budget::BudgetSlice`). Was the intent to
   eventually replace the executor's local slice with a call
   into `coord::BudgetCoordinator::try_debit`? Or are the two
   sides meant to remain decoupled, with the
   `BudgetCoordinator` only operated at epoch boundaries
   (rebalance) and the executor running its own local cache?
   If the latter, where does the executor cache come from on
   startup, and how is it kept consistent with the coordinator
   between rebalances?

3. **Signature verification gaps.** Two paths in `budget.rs`
   accept signed artefacts but do not verify the signature:
   (a) `BudgetCoordinator::rebalance_inner` does not verify
   `SpendingCertificate.signature`; (b)
   `FastUnlockManager::apply_unlock_certificate` does not
   verify the individual `UnlockVote.signature`s. Both are
   plausibly oversight rather than deliberate, given that the
   signing methods (`certificate`, `vote_unlock`) carefully
   produce real Ed25519 signatures. Is closing these gaps an
   accepted near-term task?

4. **Shared resource budget production timeline.**
   `SharedResourceBudget` is design-complete, well-tested, but
   has zero production consumers. Is the plan to wire it into
   intent settlement, AMM swaps, or multi-sig spend paths? Or
   is it a parking-lot module waiting for the right consumer?

5. **Atomic-2PC and intent settlement.** The intent crate has
   its own clearing path (`intent::trustless`,
   `intent::solver`). Should matched-intent settlement run
   over `coord::Coordinator` to gain atomic multi-party
   semantics? If so, the participant set would be the n
   parties whose intents match, and the threshold would be n.
   This seems like the natural high-value composition.

6. **Crash recovery for in-flight proposals.** Node state
   holds `atomic_proposals` in memory only. A node restart
   loses all proposals in flight. Is this intentional (relying
   on gossip restart), or should we WAL the proposal envelope
   to redb? The participants have already cryptographically
   committed to their votes by signing; in principle a fresh
   coordinator could resume collecting votes if the
   coordinator's identity was rotated.

7. **Coordinator and Participant signing keys.** Today
   `Coordinator::new` takes a 32-byte signing key directly,
   and so does `Participant::new`. These are the node's gossip
   keys (api.rs:2361, 2675). Is binding 2PC-protocol identity
   to gossip identity the right call, or should there be a
   distinct 2PC-protocol key per node for key-rotation
   hygiene?

8. **What is `Coordinator::node_id` semantically?**
   `node_id` and `silo_id` are used interchangeably in
   different parts of the codebase. `node::state.silo_id`
   feeds `Coordinator::new`'s `node_id` parameter (api.rs:2410).
   The Stingray budget code uses `SiloId = [u8; 32]` as a
   separate type alias for clarity. Is the equivalence
   (silo_id == node_id == pubkey-hash) a stable invariant?
   If a node ever runs multiple silos, this assumption
   breaks.

---

## §8. Recommendations

### Keep (load-bearing, in production)

- `atomic.rs` — the 2PC state machine is small (~1.1 KLOC),
  well-tested (1.9 KLOC of integration tests in `tests.rs`),
  and actively driven by the node HTTP API. Do not refactor.
- `serde_sig.rs` — small, focused, correct.
- `error.rs` — fine as-is.
- `budget.rs` — keep the bounded-counter primitives; node
  already depends on the type API.

### Refactor (after addressing open questions)

- **`budget.rs`**: close the two signature-verification gaps
  (§7 question 3). Add adversarial tests that confirm a
  fabricated certificate and a fabricated unlock vote are
  rejected. **Priority: high.** This is a real Stingray-
  protocol-correctness gap, not a cosmetic one.
- **`causal.rs`**: either wire `CausalLedger` into node (so
  the wrappers earn their keep) or delete them and have
  demo-agent use `pyana_types::CausalDag` like the rest of
  the workspace. The current state — wrappers exist, but no
  production code uses them — is worse than either
  alternative. **Priority: medium.**
- **`turn::budget_gate::BudgetSlice`** vs
  **`coord::budget::BudgetSlice`** duplication: either accept
  the duplication and document it explicitly in both files,
  or restructure the dep graph (e.g., move `BudgetSlice` into
  `pyana-types`) so a single definition can be shared.
  **Priority: low.** The duplication is small and structural.

### Promote (add documentation, no code change)

- Add `AUDIT-coord.md` (this file) to the workspace-level
  index. The BACKWATER audit flagged the gap; this discharges
  it. The next read of the codebase should pick this up via
  the document set, not by re-tracing the source.
- Name the Stingray lineage explicitly in `budget.rs` (cite
  paper title + authors as well as arXiv id). Same for the
  COD lineage in `shared_budget.rs`.
- Document the Layer-1 / Layer-2 interaction explicitly per
  TODO #15 (causal.rs:367–371). The interaction model is:
  Layer 2 produces a single Turn that gets executed and
  generates a receipt; that receipt then enters Layer 1's
  causal DAG via the node's normal append-path. The two layers
  share data (the Turn) but do not share state — Layer 2
  treats the executor as a black box.

### Merge (consolidation candidates)

- `coord::budget` and `audit::budget` should not be merged
  (see §3). But the workspace would benefit from a top-level
  `BUDGETS.md` that names both, states the boundary, and
  describes how a single token-presentation event would
  produce both an audit `UsageEvent` and a coord
  `try_budget_debit`. **Priority: medium.**
- `SharedResourceBudget` and `BudgetCoordinator` share enough
  math (`ceiling = balance * (f+1) / (2f+1)`,
  `compute_*_ceiling` is the same arithmetic) that a small
  shared helper would not hurt — but the BFT-threshold
  difference (3f+1 vs 2f+1) and the different proof artefacts
  (SpendingCertificate signed vs blocklace-derived) justify
  keeping them as separate types. **Do not merge the types**;
  do extract `fn bounded_counter_ceiling(balance: u64, f:
  u64) -> u64` into a tiny private helper.

### Demote (deprecate)

None outright. Every module has a defensible reason for
living. But:

- `CausalLedger`, `CausalTurn`, `CausalTurnBuilder` are the
  closest to deprecation candidates. They are well-written but
  not pulled into production. A real fix is either to
  integrate them (preferred — replace
  `node::state::ledger: Ledger` with
  `node::state::causal_ledger: CausalLedger` so that every
  receipt automatically enters the DAG) or to fold their logic
  into `pyana_types::CausalDag` and remove the wrappers.

### Rename (clarity)

- `BudgetCoordinator` → `BoundedCounterCoordinator` or
  `StingrayCounter`. The name "BudgetCoordinator" collides
  with the natural meaning of `audit::budget::BudgetEnforcer`
  and reads as more general than it is. See §3.
- `CoordError::NoParticipants` is misused as
  `NoInitiator` in `AtomicForestBuilder::build()`. Add a
  `MissingInitiator` variant.

---

## Appendix A — file checksums and line counts

```
   1113  coord/src/atomic.rs
   1237  coord/src/budget.rs
    408  coord/src/causal.rs
    221  coord/src/error.rs
     67  coord/src/lib.rs
     25  coord/src/serde_sig.rs
   1897  coord/src/shared_budget.rs
   1897  coord/src/tests.rs
   6865  total
```

## Appendix B — public type inventory

Re-exported from `lib.rs`:

```
atomic::{AbortMessage, AtomicForest, CommitMessage,
         Coordinator, CoordinatorState, Decision,
         Participant, ProposeMessage, Vote}
budget::{BudgetCoordinator, BudgetError, BudgetSlice,
         FastUnlockManager, UnlockCertificate, UnlockRequest}
causal::{CausalDag, CausalLedger, CausalTurn}
error::CoordError
shared_budget::{DebitResolution, ResourceState,
                SharedBudgetError, SharedBudgetObserver,
                SharedResourceBudget}
```

Non-re-exported but `pub`:

```
atomic::AtomicForestBuilder
budget::{ComputronBudget alias, BudgetVersion, DebitDigest,
         ResourceAmount, SiloId, LockStatus,
         SpendingCertificate, UnlockVote}
causal::CausalTurnBuilder
shared_budget::{AgentAllowance, ExtractedDebit,
                ParticipantId, ResourceId,
                encode_debit_payload,
                extract_debit_for_resource,
                extract_resource_debit}
serde_sig (private module; used via `#[serde(with = ...)]`)
```

## Appendix C — TODO/FIXME inventory

- `coord/src/causal.rs:367` — `TODO(#13)`: concurrent turn
  conflict detection tests.
- `coord/src/causal.rs:368` — `TODO(#14)`: recovery-after-crash
  tests.
- `coord/src/causal.rs:369–371` — `TODO(#15)`: cross-layer
  documentation. **Partially discharged by §1 + §4 of this
  audit.**
- `coord/src/budget.rs:1015–1017` — comment in test
  (`test_rebalance_rejects_overspend_certificate`) confessing
  "Forged signature (not verified in rebalance yet)." This is
  the §7 question 3 gap, surfaced in test code.

No FIXMEs or `unimplemented!()` calls were found in the
crate's production code.

## Appendix D — Stingray paper details

For future audit-document writers who want to confirm the
lineage:

- **Title:** Stingray: Fast Concurrent Transactions Without
  Consensus
- **Authors:** Srivatsan Sridhar, Alberto Sonnino, Lefteris
  Kokoris-Kogias, et al. (paper has multiple authors;
  exact list per arXiv abstract page)
- **arXiv:** 2501.06531
- **Year:** 2025
- **Core idea relevant to pyana:** the *bounded counter*
  primitive with `ceiling = balance * (f+1) / (2f+1)` per
  silo, plus the *fast unlock* protocol for 2PC abort
  recovery.

The pyana implementation in `budget.rs` faithfully transcribes
the math; the divergences from the paper (per §2 of this
audit) are (a) missing signature verification on certificates
and unlock votes, and (b) no production wire-up of the
coordinator to the executor's hot path.

— end of AUDIT-coord-crate.md —

# Audit: Blocklace Consensus Soundness

## Scope and starting context

Pyana's live BFT consensus lives in `blocklace/`. The earlier
`AUDIT-morpheus-federation-blocklace.md` established that
`pyana-federation::{node,transport}` is a dead in-process simulator and
`pyana-blocklace` is the only consensus engine actually wired into the
running node (`node/src/main.rs --consensus blocklace`, the only accepted
value). `AUDIT-morpheus-federation-blocklace-phase3a.md` classified the
dead-code consumers. This audit goes deeper on blocklace itself.

Read-only audit. No code is edited; only this `AUDIT-*.md` is committed.

Crate layout (`blocklace/src/`):

| Module             | Lines | Role                                                       |
| ------------------ | ----: | ---------------------------------------------------------- |
| `lib.rs`           |   453 | "Ordering Blocklace": minimal DAG container used by `tau` |
| `finality.rs`      |   950 | "Finality Blocklace": signed-block DAG, equivocation, CRDT |
| `ordering.rs`      | 1682  | Cordial Miners `tau` (wave/leader/ratification/order)      |
| `constitution.rs`  | 2303  | Constitutional Consensus (membership amendments, H-rule)  |
| `dissemination.rs` | 2077  | Cordial Dissemination (push/pull/frontier exchange)        |
| `cross_reference.rs` | 772 | Phase-4 cross-group references / DAG-delivered proofs     |
| `delegation.rs`    |   950 | Off-strand delegation primitives (not central to BFT)      |
| `pyana_bridge.rs`  |   207 | Execution-tier classifier + receipt extractor              |
| `finality_tests.rs`|   698 | Tests for finality.rs                                      |

## 1. What kind of consensus is it?

A DAG-based BFT in the **Cordial Miners** family
(arXiv:2205.09174), bolted to a Blocklace data structure
(arXiv:2402.08068), with membership amendments from **Constitutional
Consensus** (arXiv:2505.19216). Comments at the top of
`finality.rs` and `ordering.rs` cite all three papers.

Concrete shape:

- **Blocks**: Ed25519-signed, content-addressed by BLAKE3, with
  `predecessors: Vec<BlockId>` (multiple hash pointers, not a single
  parent). Each creator runs a virtual chain numbered by a per-creator
  monotonic `seq`. (`finality.rs:75-89`.)
- **Local view**: a `Blocklace` is a CRDT — `merge()` is a union over
  causally-closed deltas (`finality.rs:599-650`).
- **Ordering**: the `tau` function in `ordering.rs:410-482`.
  - Compute the **round** of each block as 1 + max(predecessor rounds)
    (`compute_rounds`, `ordering.rs:51-111`).
  - Group rounds into **waves** of fixed `wavelength` (default 3,
    `OrderingConfig::default`).
  - Each wave has a **leader** chosen round-robin by participant index
    over the current participant slice
    (`wave_leader`, `ordering.rs:167-170`).
  - A leader block at the wave's first round is **super-ratified** when
    a supermajority (`(n*2)/3 + 1`) of distinct participants have
    wave-end-round blocks that ratify it
    (`is_super_ratified`, `ordering.rs:240-278`).
  - Ratification at a block = "a supermajority of participants have a
    block in my causal past that approves the leader"
    (`ratifies`, `ordering.rs:206-234`).
  - Approval = leader is in my causal past AND no equivocation by the
    leader's creator is visible in my causal past
    (`approves`, `ordering.rs:184-200`).
  - For each finalized leader, take the union of causal pasts of
    ratifying wave-end blocks ("coverage"), subtract any previous
    leader's coverage, filter out blocks from equivocators, and
    deterministically topologically sort by block-ID (`xsort`,
    `ordering.rs:345-400`). Concatenate per-leader segments to get the
    total order.

Variants exist:

- `tau_with_config` — same but tunable `wavelength`.
- `tau_with_constitution(_and_config)` — uses
  `constitution.participants` as the participant slice.
- `tau_unified(blocklace, &ReferenceGroup, &config)` — a single shared
  blocklace can host multiple "reference groups" (sub-federations); each
  group runs the tau pipeline filtered to its participant strands, with
  rounds computed only over participant blocks
  (`compute_rounds_filtered`, `ordering.rs:618-697`). Used by
  `node/src/multi_group.rs` for the Phase-4 multi-group story.

So the algorithm is concretely: **Cordial Miners over a blocklace DAG**,
not Reservoir, not bare cordial-dissent, not a bespoke variant. The
dissemination protocol (push known causally-closed deltas, pull missing
predecessors, exchange frontiers) is also Cordial Miners verbatim
(`dissemination.rs:1-22`).

## 2. Safety property

The intended safety story (`lib.rs:1-30`):

- DAG is self-validating: each block's ID is BLAKE3 over signed content;
  rewriting history requires breaking BLAKE3 (collision resistance is
  taken as an assumption).
- Finality is monotone: `FinalityLevel` rises `Local < Bilateral <
  Attested < Ordered`, never regresses (`finality.rs:114-124`,
  `finality_never_regresses` test at `finality_tests.rs:463-491`).
- Safety bound is the standard BFT one: at most `f` Byzantine faults out
  of `n = 3f+1`, supermajority threshold `2f+1` enforced as
  `(n*2)/3 + 1` in `supermajority_threshold` (`ordering.rs:173-175`).
- Equivocation is **detectable evidence**, not just "honest nodes ignore":
  `detect_equivocation` finds two blocks with identical
  `(creator, seq)` and different content
  (`finality.rs:657-670`). The two conflicting blocks ARE the proof
  (`EquivocationProof` struct, `finality.rs:127-132`).
- Cordial Miners safety theorem (paper) says: if at most `f`
  participants are Byzantine and at most one leader per wave is
  super-ratified by an honest observer, then every honest observer
  computes the same finalized prefix. The code's contribution to this
  is:
  1. `compute_rounds` is deterministic from the DAG (Kahn's algorithm
     with explicit ordering).
  2. `approves` rejects leaders by equivocating creators
     (`ordering.rs:184-200`).
  3. `xsort` breaks ties on block ID, so two honest observers with the
     same DAG produce the same total order (`test_concurrent_blocks_deterministic_tiebreaker`,
     `ordering.rs:1025-1059`).

What is **proven in code**: only what the unit tests cover (see §7).
There is no formal verification, no model checker, no spec/Coq/TLA+
proof. The code IS the spec.

Significant safety **gaps** found while walking the code:

- **A. Two parallel `Block` types, one stripped of its signature.**
  The live consensus loop maintains a `pyana_blocklace::finality::Blocklace`
  (the signed/equivocation-aware one), but `ordering::tau` operates on
  `pyana_blocklace::Blocklace` from `lib.rs` (no signatures, no
  equivocation set). `node/src/blocklace_sync.rs:381-426
  build_ordering_blocklace` converts every finality block into an
  "ordering block" by calling `pyana_blocklace::Block::new(...)` which
  per `lib.rs:134-147` produces a block with `signature: [0u8; 64]`.
  Signatures are verified once at receive time (`finality.rs:540`) and
  then discarded for ordering.
  - This is **not** a soundness violation per se: the finality blocklace
    is the source of truth, and a Byzantine participant can't smuggle
    an unsigned block past `receive_block`. But the architectural
    contract is non-obvious; any code that ever runs `tau` over a
    blocklace whose blocks came from a less-validated source (e.g., a
    test, a future feature) would silently lose authenticity. The
    `pyana_blocklace::Block::id()` even hashes WITHOUT the signature
    (`lib.rs:118-131`), so the two BlockId namespaces are not
    interchangeable — `blocklace_sync.rs` maintains a bidirectional
    `HashMap` to translate between them. This is brittle.

- **B. Equivocation models disagree across modules.**
  - `finality::detect_equivocation` defines equivocation as "same
    `creator` + same `seq` + different content" (`finality.rs:657-670`).
  - `ordering::has_equivocation_in_past` defines it as "same
    `creator` produces ≥2 blocks at the same **round** (DAG depth)"
    (`ordering.rs:120-141`).
  - These are different equivalence classes: a Byzantine node can
    legally bump its `seq` for each forked block (no `seq` reuse) while
    still producing two blocks at the same round in the DAG. The
    finality-layer wouldn't flag them; the ordering-layer would. The
    inverse (same seq, different round depths because of skewed
    predecessor sets) is also possible. The two layers should agree on
    what counts as misbehavior.
  - In the live path, the finality-layer check runs at receive time and
    populates `equivocators`; the ordering-layer check runs inside
    `tau`. So in practice, a finality-detected equivocator's blocks may
    still appear in `tau` output if the round-based check doesn't flag
    them. Conversely, `tau` itself does NOT consult `lace.equivocators`
    — `ordering.rs` doesn't have access to that set, only to
    round-level equivocation visible in causal pasts.

- **C. `merge()` swallows equivocation silently.**
  `finality.rs:627-632`: on equivocation detected during a delta merge,
  the code inserts the offending block as evidence, sets
  `equivocators.insert`, and `continues` — discarding the
  `EquivocationProof` (`let _ = proof;`) and returning `Ok(())`. The
  test `merge_equivocator_blocks_marks_equivocator`
  (`finality_tests.rs:680-698`) asserts this is the intended behavior.
  Crucially, **`merge` does not remove the equivocator's tip**, unlike
  `receive_block` (`finality.rs:556`). It also does not stop
  `should_update_tip` from running on subsequent blocks from the same
  equivocator in the same merge call (`finality.rs:634-643`): the
  `equivocators` set is updated, but the `should_update_tip` block
  doesn't consult it. (`receive_block` line 567 does consult it.) So a
  malicious peer that delivers `[good_seq1, equivocating_seq1,
  good_seq2]` in one delta will end up with `tips[creator] = good_seq2`
  after the merge — even though the creator is now in `equivocators`.
  This is a latent bug. Effect on `tau` is partial: `tau`'s
  round-level check would still exclude the equivocator's blocks if
  the round-based equivocation is visible in the causal past. But tip
  state used elsewhere (frontier, dissemination, multi-group block
  creation) is wrong.

- **D. The federation BLS-attested root is disconnected from
  consensus.** `node/src/blocklace_sync.rs` reads `store.latest_attested_root()`
  to derive a height for the executor (`blocklace_sync.rs:1205-1212`,
  `1290-1300`), but **nothing in production writes attested roots**.
  `grep -rn "\.store_attested_root\b"` returns only tests
  (`store/src/tests.rs`). The federation crate's BLS quorum-cert
  machinery (`federation/src/checkpoint.rs`,
  `federation/src/threshold.rs`) is fully implemented but only invoked
  by `demo/sdk-consensus` and the dead simulator path. **No live code
  path ties an `AttestedRoot` to a specific blocklace point.** The
  executor receives `block_height = 0` for every turn in practice.
  This is the central composition seam between BFT ordering and
  federation attestation, and it is **not wired**.

- **E. The `Ordered` finality level is never reached in production.**
  `FinalityTracker::mark_ordered` is the only producer of
  `OrderingState::ordered`. A search across the whole tree:
  `mark_ordered` is called only from `blocklace/src/finality_tests.rs`
  and `preflight/src/checks/blocklace.rs`. **No code path calls
  `mark_ordered` after `tau` finalizes a block.** Consequently
  `PyanaBlocklaceBridge::process_finalized` (`pyana_bridge.rs:175-201`,
  which reads `blocklace.finality.ordering.ordered`) would return
  nothing on a live node — but that method is never called by the live
  node either. The actual production path is
  `BlocklaceHandle::poll_finalized_blocks` (`blocklace_sync.rs:238-314`)
  which calls `tau` directly, owns its own `executed_up_to` cursor, and
  bypasses the `FinalityTracker` entirely. The `finality.ordering.attested` and
  `finality.ordering.ordered` fields are checkpointed
  (`blocklace_sync.rs:1344-1345`) but they remain empty. The `Ack`
  payload (`finality.rs:46`) which would drive `record_ack` →
  `Bilateral`/`Attested` is also never emitted in the live path — grep
  for `Payload::Ack` shows zero call sites that produce one in
  production (only `Payload::Turn`, `Payload::MembershipVote`, and
  `Payload::Checkpoint` are written by `blocklace_sync.rs`).
  - Practical implication: the elaborate `FinalityLevel` machinery
    (Local/Bilateral/Attested/Ordered) is **vestigial**. Real finality is
    "in tau's output / not in tau's output", binary. The four-level
    progression is API surface that no live code drives.

## 3. Liveness property

Liveness follows the Cordial Miners paper: under **partial synchrony**,
once messages are delivered, leaders are eventually super-ratified and
`tau` advances. The implementation chooses wavelength = 3 rounds (the
"eventual synchrony mode" per `ordering.rs:36`), which is the paper's
default.

What the implementation actually guarantees:

- Dissemination is **quiescent** (`blocklace_sync.rs:73`, comment "no
  messages when idle"). Receivers wake via `Notify` (`spawn_finality_executor`,
  `blocklace_sync.rs:1037-1041`). So liveness is purely event-driven.
- `cordial dissemination` enforces causal closure on every delta
  (`dissemination.rs:18-22`), and chunks pushes at 100 blocks max
  (`dissemination.rs:32`). This bounds memory but doesn't bound
  catch-up time.
- Wave advancement is decoupled from real time: `advance_constitution_wave`
  bumps `current_wave` once per `poll_finalized_blocks` batch
  (`blocklace_sync.rs:1129-1132`). With wavelength=3, three rounds of
  blocks must be produced (by a supermajority of participants) before
  the next leader can be finalized. With one participant (solo mode),
  every block trivially has supermajority and finalizes immediately
  (special case at `blocklace_sync.rs:249-261`).

Failure modes:

- **Partition**: each side keeps producing blocks on its own strands,
  but no leader can be super-ratified without a supermajority of
  distinct participant strands acknowledging it. `tau` returns an empty
  (or unchanged) finalized prefix. When the partition heals, dissemination
  merges the two halves; if a leader's wave eventually accumulates a
  cross-partition supermajority, finalization resumes. Test:
  `dissemination.rs:1445-1486 partition_and_merge_via_delta_exchange`
  exercises merge after partition but does NOT test that `tau` advances
  after heal — only that the DAG converges.
- **Missing leader**: `ordering.rs:1074-1107 test_missing_leader_wave_skipped`
  confirms that if the designated leader produces no block at the
  wave's first round, that wave finalizes nothing (`result.is_empty()`).
  Followers' subsequent waves can still finalize when their leaders
  appear, but the absent leader's wave is permanently skipped. There is
  **no view change**: if leader L is silent for waves where L is the
  round-robin choice, those waves stay unfinalized until the
  Constitution's `timeout_waves` machinery
  (`constitution.rs:582-649 check_timeouts`) evicts L and shrinks the
  participant set. Effective time-to-progress = `timeout_waves * wavelength
  + voting time`. Default `timeout_waves` is configurable (10s default
  per `blocklace_sync.rs:59 DEFAULT_CONSTITUTION_TIMEOUT_MS`, but
  `timeout_waves` is set by the caller, not millis).
- **Sleepy validator**: explicitly handled. The "sleepy validator"
  comment is at `constitution.rs:566-567`. Timed-out participants are
  proposed for `MembershipProposal::Leave`, voted on by the remaining
  active participants, and removed when the proposal passes. The
  threshold drops with each eviction. Three anti-oscillation guards:
  `min_membership_duration` (newly joined nodes get grace),
  `rejoin_grace_waves` (re-joined nodes get extra timeout), and
  `partition_detection` (freezes membership changes if >50% time out
  simultaneously, `constitution.rs:610-616`).
- **Adversarial leader silence**: a Byzantine leader can stall its own
  wave indefinitely. The recovery is only via timeout-eviction, which
  takes at least `timeout_waves` waves to detect and a full vote round
  to apply. Not catastrophic, but slow.

So liveness is: progress under partial synchrony + supermajority
honest + no persistent adversarial leader-of-the-wave. Under partition,
no progress until heal + at least one supermajority leader is
produced.

## 4. Equivocation handling

The two views (§2 gap B) agree on the punishment but disagree on the
detection rule:

- **finality.rs (receive-time)**: same `(creator, seq)`, different
  content → `Err(BlockError::Equivocation { proof })`. `receive_block`
  adds the creator to `equivocators`, removes their tip
  (`finality.rs:553-564`). Subsequent blocks from this creator can be
  received and stored but **do not update tips**
  (`finality.rs:566-579`). Their blocks remain in `self.blocks` so the
  equivocation proof is retained.

- **ordering.rs (during tau)**: same `(creator, round)`, two distinct
  blocks → `has_equivocation_in_past` returns true
  (`ordering.rs:120-141`). Any block whose causal past contains this
  pattern fails `approves` (`ordering.rs:184-200`). The equivocating
  leader's wave is consequently never super-ratified, and ALL blocks by
  the equivocator are excluded from the finalized order
  (`tau_with_config` filter at `ordering.rs:462-473`).

- **constitution.rs (eviction)**: `Constitution::auto_evict_equivocator(&proof)`
  removes the equivocator from `participants` **immediately**, no vote
  required, increments the version (`constitution.rs:168-178`). This
  is the slashing-equivalent: the cryptographic proof is self-evident,
  so consensus is not needed to apply the punishment. `ConstitutionManager::auto_evict`
  also clears their activity and timeout state
  (`constitution.rs:512-522`). Eviction is durable (the change goes
  into the `history` vector for back-dating later block validity
  checks).

So: **no slashing of stake** (there is no stake model), but **immediate
permanent eviction with proof retained**. Honest nodes who later receive
the equivocator's blocks will also independently detect the
equivocation and evict, because both blocks are signed and replayable.
The two-block proof is the slashing evidence.

Test coverage:
- `finality_tests.rs:83-107 detect_equivocation_same_seq`
- `finality_tests.rs:109-123 fork_equivocation_detection`
- `finality_tests.rs:496-553 remove_equivocator_excludes_from_tips`,
  `equivocator_blocks_dont_update_tips`
- `finality_tests.rs:680-698 merge_equivocator_blocks_marks_equivocator`
- `ordering.rs:971-1023 test_equivocating_block_excluded`
- `constitution.rs:1253 auto_eviction_equivocator_immediately_removed`

What is **NOT tested**:
- The seq-only-equivocation-vs-round-only-equivocation discrepancy
  (gap B). A Byzantine node forking with strictly increasing `seq`
  numbers wouldn't be caught by `detect_equivocation` but might still
  be excluded by `tau`'s round check. No test exercises this corner.
- `merge`'s failure to remove tips on equivocation (gap C). The
  existing `merge_equivocator_blocks_marks_equivocator` test only
  checks that `is_equivocator(creator_b)` and `len() == 2` — it does
  not assert anything about `tips`.

## 5. Composition with federation

There are **two** federation concepts in the tree:

1. The blocklace's own "federation" = the `Constitution`'s
   `participants` list. This is the consensus participant set;
   amendments are blocklace-level governance with the H-rule applied
   for threshold changes (`constitution.rs:94-104`). This is what
   `tau` uses.

2. The `pyana-federation` crate's BLS threshold attestation
   (`federation/src/threshold.rs`, `federation/src/checkpoint.rs`).
   Live consumers from `pyana-federation` that the running node
   actually uses are: `solo::FederationMode`, `SoloConsensusState`,
   `NullifierLog`, `quorum_threshold(n)`, `fault_tolerance(n)`,
   `threshold`, `threshold_decrypt`, `checkpoint`, `revocation`,
   `epoch`, `types::*` (per AUDIT-morpheus phase 3a).

How they compose: **they don't, in production.** See gap D in §2.

The `Constitution` is the only "federation" the blocklace knows about;
its `routes_commitment` field (a BLAKE3 hash of the routing DFA) is
optional, and amendments to it pass through the same proposal/vote
mechanism (`constitution.rs:139-159`). The BLS threshold attestation
infrastructure (`FederationCommittee::sign_checkpoint`, etc.) is built
out but its only live caller is the test/demo path.

A real composition (federation attests a blocklace point) would look
like: after `tau` finalizes a prefix ending at block B with content
hash H, the federation members produce a `ThresholdQC` over `(H,
block_height, B)`, sign with their BLS shares, aggregate, and
`store_attested_root(StoredAttestedRoot { root: H, height: B.height,
qc: aggregated })`. None of this exists today.

The closest live wiring is in `node/src/multi_group.rs` (the unified
multi-group blocklace), where each `GovernedReferenceGroup` is itself
a federation-like quorum view. `cross_reference::DagDeliveredProof`
allows STARK proofs to ride on blocklace blocks
(`cross_reference.rs:55-68`), so a group's finalization implicitly
witnesses the included proofs — but again, no separate BLS attestation
step.

## 6. Composition with `TurnExecutor`

The seam is `node/src/blocklace_sync.rs` (in particular
`execute_finalized_turn`, lines 1157-1278). Walking it:

1. Caller submits a turn via the HTTP API. The API path constructs a
   `Payload::Turn(serialized_signed_turn)` and calls
   `blocklace.add_block(payload)` on the local strand
   (`finality::Blocklace::add_block`, `finality.rs:500-508`). The new
   block uses ALL CURRENT TIPS as predecessors
   (`finality.rs:502`).
2. The new block is gossiped via `BlocklaceGossipMessage::Push` over
   the `pyana/blocklace` gossip topic (`blocklace_sync.rs:44`).
3. Peers receive, `receive_block` runs signature/closure/equivocation
   checks, and they may produce their own blocks acknowledging the new
   one in their causal past.
4. Periodically (driven by `finality_notify`), each node runs
   `BlocklaceHandle::poll_finalized_blocks`
   (`blocklace_sync.rs:238-314`). This:
   - Converts the finality-layer blocklace to an ordering-layer
     blocklace (`build_ordering_blocklace`, lines 381-426).
   - Runs `tau(&ordering_lace, &participants)` (line 267).
   - Translates ordering-BlockIds back to finality-BlockIds via the
     `id_map` returned by the build helper.
   - Returns blocks at positions `[executed_up_to ..]` of the ordered
     prefix, advancing the cursor.
5. `spawn_finality_executor` (lines 1036-1151) consumes the
   `FinalizedBlock`s. For each `FinalizedBlock::Turn`:
   - Deserialize as `pyana_sdk::SignedTurn` (line 1164).
   - Verify the turn's Ed25519 signature against the signer's public
     key (line 1177-ish, just past the snippet).
   - Set `executor.set_timestamp(now)` and
     `executor.set_block_height(latest_attested_root().height)` —
     this is gap D again: `block_height = 0` in production.
   - Call `executor.execute(&signed_turn.turn, &mut state.ledger)`.
   - On `TurnResult::Committed`, persist the receipt, fire
     `NodeEvent::Receipt`. On `Rejected`, log and skip.

So a turn becomes "consensus-committed" the moment
`poll_finalized_blocks` emits a `FinalizedBlock::Turn` for its block ID,
AND the executor produces `TurnResult::Committed`. The receipt itself
is a `pyana_turn::TurnReceipt` which lives in the cclerk and emits a
WebSocket event; **the receipt is not re-embedded as a new blocklace
block** (no on-chain receipt feedback). Receipts may be signed by the
executor (`maybe_sign_receipt` in `turn/src/executor.rs:762`), but the
signed receipt does not flow back into consensus.

Net: the executor seam is clean and one-way. Consensus orders blocks,
executor consumes the ordered turn data deterministically. The only
fragile part is the dual Block-type translation (gap A) and the always-
zero `block_height` (gap D).

## 7. Test coverage

Total `#[test]` count across `blocklace/src/`: **199** unit tests.

| File                | Tests |
| ------------------- | ----: |
| `lib.rs`            |   ~8  |
| `finality_tests.rs` |  ~32  |
| `ordering.rs`       |  ~42  |
| `dissemination.rs`  |  ~43  |
| `constitution.rs`   |  ~47  |
| `delegation.rs`     |  ~29  |

Highlights of what's covered:

- **CRDT properties**: associativity, commutativity, idempotency of
  `merge` (`finality_tests.rs:218-300`).
- **Equivocation detection** at receive and during merge
  (`finality_tests.rs:83-123`, `680-698`).
- **Closure enforcement**: missing-predecessor errors
  (`finality_tests.rs:128-139`).
- **Causal-past computation** and `is_predecessor` relation
  (`finality_tests.rs:144-178`).
- **Large-scale merge**: 100 creators × 10 blocks
  (`finality_tests.rs:305-340`).
- **Ordering determinism**: same DAG → same tau output, concurrent
  blocks sort by ID (`ordering.rs:1025-1059`).
- **Multi-wave finality**: 6 rounds → 2 waves → 18 blocks ordered
  (`ordering.rs:1062-1071`).
- **Missing leader**: wave skipped, output empty if leader absent
  (`ordering.rs:1074-1107`).
- **Monotonicity**: extending the DAG never reorders previously
  finalized blocks (`ordering.rs:1110-1170+`).
- **Equivocator exclusion** from tau output (`ordering.rs:971-1023`).
- **Constitutional auto-eviction** on equivocation proof
  (`constitution.rs:1253-…`).
- **Partition + heal**: delta exchange after partition produces
  identical DAGs (`dissemination.rs:1445-1486`).

Adversarial / fault-injection coverage:

- The blocklace crate has tests for **single-node misbehavior**
  (equivocation, byzantine leader absence) and **CRDT-shaped network
  faults** (delivery reorder, duplicate delivery).
- It does **not** have tests for:
  - Coordinated multi-node Byzantine behavior (e.g., n-1 nodes
    colluding to force a specific tau output).
  - Network adversary (drop, delay, reorder beyond standard merge
    commutativity) — `teasting/src/fault.rs` has the
    `FaultyNetwork`/`MessageBuffer` primitives but they operate on
    `WireMessage` and do NOT run blocklace consensus (the dead Morpheus
    simulator is what `teasting` drives).
  - Concurrent network partition + membership change (would a partition
    detected by `check_timeouts` interact correctly with an in-flight
    vote?). No test combines `partition_detection = true` with a
    pending `MembershipProposal`.
  - The two parallel `Block` types (gap A): no test crosses the
    `build_ordering_blocklace` boundary with intentionally bad data.
    `tau` is tested in isolation with hand-built ordering blocks; the
    finality layer is tested with hand-built signed blocks; the bridge
    is implicit.
  - Federation BLS attestation interacting with tau output (gap D):
    no test, because no production code wires it.

## 8. Known gaps

No `TODO`/`FIXME`/`HACK` markers anywhere in `blocklace/src/` (grep
across the whole crate is empty). The crate presents as finished work.
But, from §2 onwards, the practical gaps are:

- **A. Dual Block-types / lossy translation seam** (`lib.rs` Block has
  no signature; `build_ordering_blocklace` strips signature). Brittle.
- **B. Two equivocation definitions** (seq-based in finality, round-
  based in ordering) that can disagree on a given Byzantine pattern.
- **C. `merge` does not remove tips for equivocators**, unlike
  `receive_block`. Latent bug; effect depends on what reads `tips`.
- **D. No production wiring of federation BLS-attested roots to a
  blocklace point.** `block_height` passed to the executor is always 0
  in production. `latest_attested_root` is never populated outside
  tests.
- **E. The four-level `FinalityLevel` is vestigial.** `mark_ordered`,
  `record_ack`, `Payload::Ack` are all unused in the live path. The
  binary "in `executed_up_to` prefix vs. not" is the real finality
  signal. The dead machinery is checkpointed and restored
  (`finality.rs:818-867`) and could mislead a reader into thinking
  finality is more nuanced than it is.
- **F. No view change for silent leaders.** A Byzantine leader that
  refuses to publish its wave's leader block stalls that wave until
  the constitution's timeout-eviction (default several waves) removes
  it. Acceptable per the paper's model but slow.
- **G. The constitution's `routes_commitment` is hashed but not
  enforced.** `AmendRoutes` accepts a new DFA hash, but the audit did
  not find live code that rejects blocks violating the committed
  routes. (Out of scope of this audit to confirm in full; flagged for
  follow-up.)
- **H. Multi-group `tau_unified`** has its own filtered round
  computation but reuses the same `find_all_final_leaders` /
  `is_super_ratified` / `ratifies` functions that take a `participants`
  slice. There is no test that two reference groups with overlapping
  participant sets behave correctly under cross-group block flow. The
  test in `node/src/multi_group.rs` (line 545+) sets up disjoint
  groups.

## Soundness verdict

**The blocklace consensus engine, in the abstract Cordial Miners /
constitutional layer, is a faithful implementation of the published
algorithm and is sound under its stated BFT assumption (n ≥ 3f+1,
partial synchrony, BLAKE3 collision resistance, Ed25519 unforgeability).
Equivocation is cryptographically self-evident, leaders are
deterministically chosen, ordering is deterministic, monotone, and
CRDT-friendly. The 199 unit tests cover the bread-and-butter safety,
liveness, and CRDT properties.** That said, the AS-INTEGRATED system
has three serious unfinished seams that mean the claim "blocklace is
the live BFT consensus" is technically true but materially incomplete:
(1) the dual Block-type bridge in `blocklace_sync.rs` strips
signatures and uses a round-based equivocation rule that disagrees
with the receive-time seq-based rule — the two layers can flag
different sets of Byzantine behavior; (2) the federation BLS quorum-
attestation pipeline that would tie a finalized blocklace point to a
durable `AttestedRoot` is **fully built but never invoked in
production**, so the executor receives `block_height = 0` indefinitely
and external verifiers have no quorum-signed checkpoint to verify
against; (3) the `FinalityLevel` Bilateral/Attested/Ordered ladder
and `Payload::Ack`-driven attestation tracking are dead in the live
path — only the binary "in tau's prefix" matters, which is fine but
makes a third of `finality.rs` and all of `pyana_bridge.rs` vestigial.
Net: the **algorithm is sound, the integration is partial**. Pyana
will not produce wrong answers; it will produce CORRECT but
**unattested** answers, with brittle internal seams that a future
refactor could trip over.

## Open questions for designer

1. **Was leaving the federation BLS attestation pipeline unwired
   intentional** (i.e., not yet needed for the current demo), or is
   `store_attested_root` supposed to be called from some path I missed?
   Concretely: which component's job is it to call
   `FederationCommittee::sign_checkpoint` after `tau` finalizes a
   prefix, and where should the resulting `StoredAttestedRoot` be
   written?

2. **Should the two equivocation definitions be unified?** The seq-based
   rule (finality.rs) is cheap and correct for a normal honest
   participant who never reuses a seq. The round-based rule
   (ordering.rs) is what the Cordial Miners paper actually says. A
   Byzantine participant choosing seq monotonically across forks
   defeats one and not the other. Recommend ordering.rs's
   `has_equivocation_in_past` be augmented with the seq-based check
   from `lace.equivocators`, or vice versa.

3. **Is `pyana_bridge::PyanaBlocklaceBridge` deprecated?** It's the
   only consumer of `FinalityTracker::ordered`, which is never
   populated. Live code uses `BlocklaceHandle::poll_finalized_blocks`
   instead. If deprecated, recommend removing
   `FinalityTracker::mark_ordered`, `Payload::Ack`, and the four-level
   `FinalityLevel` to reduce confusion, or wire them up and use them.

4. **Is the dual `Block` type (lib.rs vs. finality.rs) deliberate**
   (separation of concerns: ordering vs. validation), or an artifact
   of incremental development? If the former, the contract should be
   documented; if the latter, consider merging into a single
   `pyana_blocklace::SignedBlock` that `tau` accepts directly.

5. **What is the recovery story if `tau` ever returns a different
   prefix on two honest nodes?** The algorithm's correctness proof
   says this can't happen under the BFT assumption, but if it did
   (bug, BLAKE3 collision, Ed25519 break, or 1/3+ Byzantine), there
   is no fork-choice rule to recover. Honest nodes would just
   execute different turns and silently diverge. Is there an
   integrity check that compares `executed_up_to` block hashes across
   peers?

6. **Is `merge`'s tip-handling bug for equivocators** (gap C) a real
   issue downstream, or is `tips` only used in a way where stale data
   is harmless? If harmless, recommend documenting the invariant; if
   not, recommend mirroring `receive_block`'s tip-removal logic into
   `merge`.

7. **For multi-group / cross-reference / `tau_unified`**, what's the
   safety story when two groups have overlapping participants? A
   participant could legitimately produce different blocks in different
   reference groups (different strands' state). Does
   `has_equivocation_in_past` correctly distinguish "produced two
   blocks in two groups" from "equivocated within one group"?

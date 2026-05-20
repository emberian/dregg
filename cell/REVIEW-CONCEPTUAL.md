# Conceptual Review: pyana-cell, pyana-turn, pyana-coord

> **Status (2026-05-20):** Several critical findings in this review have been FIXED:
> - Turn atomicity (section 2) now uses journal-based undo instead of full ledger clone.
> - 2PC coordinator (section 3) now verifies Ed25519 signatures on Yes votes.
> - Signature verification is now real (section 5's "None" auth concern is design-level, not a bug).
> The remaining findings (capability amplification in section 1, 2PC recovery gaps in section 3,
> causal DAG limitations in section 4) are still valid and open.

## 1. Capability Model

The c-list model is structurally correct: cells hold only explicit references, attenuation is monotonically narrowing, and transitivity requires explicit forwarding. The `is_narrower_or_equal` lattice is well-defined. However, there is a confused-deputy risk in `GrantCapability`: the executor checks that the `from` cell exists but does NOT verify that the granting cell actually holds the capability it is granting to `to`. An action targeting cell A can grant cell B a capability pointing at cell C without proving A has access to C. This is an authority amplification path. The `DelegationMode` mechanism partially mitigates this at the call-forest level, but effect application is not gated on delegation mode -- it is checked only for child action *targeting*, not for capability-grant effects within an action's own effect list.

Additionally, capabilities lack scoping: a `CapabilityRef` says "you can reach target with this auth level" but does not restrict *which actions* or *which methods* on the target. This means any capability is an all-or-nothing handle. The Mina model it draws from has per-field permissions, but here capability permissions only gate how you authenticate, not what you can do after authenticating.

## 2. Turn Atomicity

Single-turn atomicity is solid: full ledger clone-on-entry, validate-then-apply, rollback on any failure. The call-forest-as-transaction insight from Mina is well-applied. However, there is no model for long-running turns. Turns are synchronous, single-shot, and unbounded in wall-clock time (only computron-bounded). There is no concept of a turn timeout at the executor level. The `valid_until` field provides expiration semantics before execution starts, but once execution begins, there is no mechanism to abort a turn that is taking too long (relevant for ZK proof verification, which could be computationally expensive).

For retries: the nonce model gives idempotency-by-rejection (replaying a nonce fails), but there is no mechanism for "retry with the same intent but new nonce." A failed turn consumes nothing (full rollback), so the caller can construct a fresh turn, but there is no first-class retry or saga concept.

## 3. 2PC Coordinator

The 2PC design is the minimum viable protocol for cross-silo atomicity, which is appropriate for this stage. Known failure modes that are unaddressed:

- **Coordinator crash after collecting votes but before commit/abort**: participants are stuck in limbo. There is no timeout/recovery protocol and no persistent log of the coordinator's decision. The `CoordinatorState` is entirely in-memory.
- **Split-brain**: if a participant applies a commit locally but the coordinator crashes before notifying others, ledgers diverge permanently. There is no view-change or recovery protocol.
- **Phantom reads**: participants evaluate preconditions against their local ledger snapshot at vote time. Between voting and commit, causal turns from other nodes could change the ledger state, invalidating the preconditions. The coordinator re-executes the turn at commit time against its own ledger, but participants who apply the commit locally may see different state if their causal ledgers have diverged.
- **No prepare-phase locking**: participants do not "lock" their cells during the voting window, so concurrent causal turns can invalidate voted-upon preconditions.

These are all standard 2PC limitations. The design acknowledges this by being simple, but production use would need either 3PC, Paxos-based commit, or compensating transactions.

## 4. Causal Ordering

The causal DAG gives you:
- Happened-before verification between any two turns (BFS reachability).
- Concurrency detection (neither precedes the other).
- Per-node total ordering via sequence numbers.
- A frontier concept for "latest known state."

What you can prove: given a receipt and the DAG, you can demonstrate that turn T2 was produced with knowledge of T1's outcome. This is useful for accountability and audit trails.

What you cannot prove: that the ordering is consistent with real time, or that a node is not selectively withholding turns. The model is vulnerable to equivocation (a node producing two turns with the same sequence number on different forks). The sequence-gap check prevents this on a single CausalLedger instance, but not across partitioned replicas. There is no BFT mechanism here.

Also: rejected turns consume a sequence number and occupy the DAG, which is correct for accountability but means the DAG grows monotonically regardless of success. There is no pruning or checkpointing mechanism.

## 5. Permission Model Sufficiency

The `None/Signature/Proof/Either/Impossible` lattice is clean but limited:
- **No conditional permissions**: cannot express "Signature required if amount > 1000, None otherwise."
- **No time-bounded permissions**: cannot express "Signature required only after block height X."
- **No delegated permissions**: the `delegate` field on Cell points to a parent but there is no mechanism for the parent to act on behalf of the child without holding the child's signing key. The `delegate` field is stored but never checked during authorization.
- **No multi-sig**: cannot require "2-of-3 signatures."

The preconditions system partially compensates (you can gate actions on time ranges), but preconditions are per-action, not per-permission-slot. The permission model is sufficient for MVP but will need extension for production agent scenarios.

## 6. Computron Metering Fairness

Metering is deterministic and pre-declared: the fee is paid upfront, and if `computrons_used > fee`, the turn rolls back entirely. This prevents griefing at the ledger level -- a malicious turn cannot permanently consume state. However:

- **CPU-time attacks**: ZK proof verification cost is fixed at 1000 computrons regardless of actual verification complexity. A malicious agent could submit a proof that takes seconds to verify but costs the same as a trivial one. The proof verifier trait has no timeout.
- **Memory attacks**: the executor clones the entire ledger for rollback. A turn with many `CreateCell` effects could force large allocations before being budget-rejected.
- **Co-located agent DoS**: there is no per-agent rate limiting or priority. A single agent can submit back-to-back turns consuming all executor capacity. Fair scheduling is out of scope for the data model but would be needed in a runtime.

The metering model is sound for the single-turn case but needs a resource-limit layer above it for multi-tenant execution.

## 7. Comparison to E/Agoric Vat Model

The design draws more from Mina's zkApp model than from E/Agoric, which creates both strengths and gaps:

**Present (from Mina)**: content-addressed identity, Merkle-committed state, call-forest-as-transaction, per-account permissions, balance conservation.

**Missing (from E/Agoric)**:
- **Promise pipelining**: in E, messages return promises that can be pipelined without round-trips. Here, all effects must be pre-declared in the call forest. There is no way to express "call A, then use A's return value to call B" within a single turn.
- **Eventual-send queues**: E vats have persistent message queues. Here, there is no inter-cell message queue -- all communication is synchronous within a turn or requires external coordination.
- **Membrane/facet pattern**: E objects can present different facets to different callers. Here, a cell has one permission set for everyone. The breadstuff token is the closest analog but it is not a proper facet.
- **Garbage collection of capabilities**: c-list slots are never reused (monotonically increasing `next_slot`). In long-lived systems, this is a slow leak. E vats GC unreachable capabilities.
- **Confinement/transparency**: E has explicit confinement guarantees (an object cannot exfiltrate a reference it was not given). Here, an action's effects can grant any `CellId` as a capability target without proving possession, which breaks confinement (see point 1).

**Overall assessment**: the design is a well-considered hybrid of Mina's account-update model and E-style capability isolation. The cell/turn/coord layering is clean. The most critical gap is the authority amplification in `GrantCapability` (confinement violation). The 2PC coordinator is appropriate for prototyping but needs recovery semantics before any adversarial deployment. The causal DAG is useful but needs BFT hardening. The core abstractions are sound; the gaps are in the interstitial protocols rather than the fundamental model.

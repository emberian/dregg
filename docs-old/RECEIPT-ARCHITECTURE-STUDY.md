# RECEIPT-ARCHITECTURE-STUDY

A whole-system audit of dregg's receipt machinery: every shape, every
construction site, every verifier, every consumer, every drift, and a
prioritized plan for what has to land for Silver-Vision-completeness.

The framing follows the houyhnhnm reframe (see
`HOUYHNHNM-COMPARISON.md §3.1`, `HOUYHNHNM-DEEP-CRITIQUE.md §4.2`):
the `WitnessedReceipt` chain is not an *auxiliary observability log*;
it IS dregg's persistence layer — state on disk is *derivable* from
the witness stream. That reframe is generous (the system was not
*designed* that way) but it correctly names what the code, taken
seriously, is reaching toward. This document audits the gap between
that reading and what the code today actually delivers.

Read-only audit; no code touched.

---

## §1. Receipt-as-persistence framing — why this study exists

### 1.1 The houyhnhnm "wait this changes things" reframe

From `HOUYHNHNM-COMPARISON.md` §3.1 (verbatim):

> `dregg`: `WitnessedReceipt` is exactly this. The turn — the *event* —
> plus the proof that the transition was determined by the witness,
> is the persisted unit. The state on disk is *derivable* from the
> witness stream; the witness stream is the source of truth. Scope-2
> WitnessedReceipts contain the inline witness data so *any* verifier
> can re-execute the AIR.
>
> This is the central conceptual convergence. `dregg` arrived at this
> from cryptographic necessity (you can't prove a transition you can't
> replay); houyhnhnm arrived at it from "we want infinite undo and we
> hate flushing buffers." Same answer, very different motivation.
>
> The houyhnhnm framing *clarifies dregg's existing meaning*: the
> WitnessedReceipt chain is not "a log of proofs" — it is **dregg's
> persistence layer**.

If that is read as load-bearing rather than as a fortunate parallel,
several things follow:

1. **Every authoritative state change must produce a receipt.** A
   transition without a corresponding receipt is a hole in the
   persistence layer.
2. **Every soundness-meaningful fact about a transition must be
   committed by the receipt.** A fact that is enforced by the
   executor but not bound into `receipt_hash` is invisible to a
   reconstructor.
3. **Every consumer that reads receipts must check the same things.**
   Drift between verifiers = drift between "what is persisted." A
   verifier that does not enforce the chain-walk invariant is reading
   a different log than one that does.
4. **The chain-of-chains** (cross-cell, cross-federation, cross-time)
   must compose cleanly — pruning, forking, merging must all preserve
   the persistence property.

This document checks all four of these.

### 1.2 What "persistence layer" means concretely

The minimum operational test:

> Given (a) the genesis state of every cell in a federation and
> (b) the full receipt stream the federation has emitted, a
> brand-new node with no prior memory can reconstruct every cell's
> *current state*, every authority *currently held* by every actor,
> every nullifier *currently spent*, and every receipt-chain head
> *currently authoritative* — and the reconstruction is identical
> bit-for-bit on every honest node that performs it.

§8 audits whether dregg passes this test today. Spoiler: partially.

### 1.3 The codebase has a receipt-shaped hole, not a single receipt

The shocking finding (which the comparison study circled around but
the deep critique made sharp) is that there are at least **five**
different objects in the codebase that all call themselves "a
receipt," each binding a slightly different set of facts, each verified
by a different code path. They do not currently compose into one
coherent stream — they overlap and chain in places, but no global
discipline says "this is the canonical receipt shape." See §2 and §9.

---

## §2. Current shape — every receipt type, every field, every builder, every verifier

### 2.1 The taxonomy: five receipt-shaped objects

| # | Type | Defined at | Issuer | Verified by | Carried-fact set |
|---|---|---|---|---|---|
| 1 | `TurnReceipt` | `turn/src/turn.rs:526` | executor on a committed turn | `turn/src/verify.rs:117`, `verifier/src/lib.rs:477` | turn_hash, forest_hash, pre/post_state, effects_hash, computrons, action_count, prev_hash, agent, federation_id, routing/introduction/derivation/events, executor_signature, finality, was_encrypted |
| 2 | `WitnessedReceipt` | `turn/src/witnessed_receipt.rs:243` | prove-site (today `node/src/mcp.rs::generate_effect_vm_proof`) | `verifier::replay_chain` / `replay_chain_recursive` | wraps (1) + STARK proof bytes + public_inputs + optional `WitnessBundle` (inline trace, optional `RecursiveProofVariant`) + `witness_hash` + `aggregate_membership` (always `None` in v1) |
| 3 | `FederationReceipt` (+ `FederationReceiptBody`) | `federation/src/receipt.rs:42`, `federation/src/receipt.rs:123` | federation aggregator (`node/src/blocklace_sync.rs:2043`) | `FederationReceipt::verify` | turn_hash, block_height, block_hash, agent, nonce, pre_state, post_state, effects_hash, prev_hash + BLS/Ed25519 QC over the body hash, federation_id, committee_epoch |
| 4 | `BridgeReceipt` | `cell/src/note_bridge.rs:361` (per `DESIGN-receipts.md §1.1`) | destination federation on a bridge mint | `verify_bridge_receipt` against caller-supplied keys | nullifier, dest_federation, mint_height, Ed25519 sig |
| 5 | `BlocklaceTurnReceipt` | `blocklace/src/dregg_bridge.rs:119` | local blocklace bridge | (no verifier) | block_id, submitter, seq, turn_data, tier, finality_height — *not signed; local bookkeeping only* |

There are also: `AuditReceipt` (`audit/src/event.rs:76`) for Merkle
inclusion in a log; application-layer receipts (`WriteReceipt`,
`SupplyReceipt`, `DebitReceipt`, etc. in `apps/*`); and `ReceiptView` /
`ReceiptInfo` DTOs in `wasm/` and `node/` for the JS-facing layer.
Those are out of scope for the persistence-layer question because
they do not appear in the chain.

The persistence claim is really about (1) and (2): the
`TurnReceipt` chain and the `WitnessedReceipt` wrapper that lifts
each receipt into a scope-2-replayable artifact.

### 2.2 `TurnReceipt` field-by-field (`turn/src/turn.rs:526-581`)

```rust
pub struct TurnReceipt {
    pub turn_hash:            [u8; 32],        // Turn::hash() (v3)
    pub forest_hash:          [u8; 32],        // CallForest::compute_hash
    pub pre_state_hash:       [u8; 32],        // Ledger.root() before
    pub post_state_hash:      [u8; 32],        // Ledger.root() after
    pub timestamp:            i64,             // executor's wall clock
    pub effects_hash:         [u8; 32],        // BLAKE3 over runtime effects (or empty)
    pub computrons_used:      u64,
    pub action_count:         usize,
    pub previous_receipt_hash:Option<[u8; 32]>,// chain link
    pub agent:                CellId,
    pub federation_id:        [u8; 32],        // v2 binding (cross-fed replay)
    pub routing_directives:   Vec<RoutingDirective>,
    pub introduction_exports: Vec<IntroductionExport>,
    pub derivation_records:   Vec<DerivationRecord>,
    pub emitted_events:       Vec<EmittedEvent>,
    pub executor_signature:   Option<Vec<u8>>, // ed25519 over canonical msg
    pub finality:             Finality,        // Final | Tentative
    pub was_encrypted:        bool,            // privacy-path disclosure
}
```

Two hash views are computed:

- `receipt_hash()` at `turn.rs:586` — versioned `dregg-receipt-v2`,
  covers *every* field above except `executor_signature` (it would
  be circular).
- `canonical_executor_signed_message()` at `turn.rs:686` — versioned
  `executor-receipt-sig-v2`, covers only `turn_hash`, `pre_state_hash`,
  `post_state_hash`, `timestamp`, `federation_id`, `agent`.

**The gap between these two is the heart of §5.** `was_encrypted`,
`finality`, `effects_hash`, `derivation_records`, `routing_directives`,
`introduction_exports`, `emitted_events`, `previous_receipt_hash`,
`computrons_used`, `action_count`, `forest_hash` are all in
`receipt_hash` but *not* in the executor's signed message. A
verifier who trusts only the signature gets a strictly weaker
statement than one who recomputes the receipt hash. The Stage 9 R-4
docstring (`turn.rs:657-685`) acknowledges this deliberately
("downstream verifier that does not understand routing_directives,
derivation_records, etc. can still recover the executor's intent");
the deep audit's read is that this is *too narrow* — see §5.

### 2.3 Receipt construction sites in the executor

There are exactly **two** canonical `TurnReceipt {...}` literal sites
in `turn/src/executor.rs`:

- **Proof-carrying turn path** (executor.rs:4438) — used when
  `turn.execution_proof.is_some()`. The receipt is *minimal*:
  `effects_hash = compute_effects_hash(&[])`, `computrons_used = 0`,
  `action_count = 0`, `routing_directives = []`, etc. The STARK
  proof IS the validation; the receipt is essentially a stub binding
  the proof to a chain link. **Audit finding (EXECUTOR-VK-AUDIT.md §2.2):**
  the receipt structurally *claims* "zero effects applied" when the
  proof attests to a non-trivial transition. The proof verifies the
  state delta; the receipt under-reports what the proof attested.

- **Classical / mixed-effect path** (executor.rs:4898) — used for
  every turn that goes through the call-forest interpreter. Carries
  the full effect-applied bookkeeping.

Both sites flow into the same `record_receipt_hash` /
`maybe_sign_receipt` post-processing.

A **third "site"** exists outside the executor: the encrypted-turn
adapters at executor.rs:1196 (`execute_encrypted_turn`) and
executor.rs:1282 (`apply_encrypted_turn`). They do not build receipts
de novo — they delegate to `execute()` and then **mutate** the
returned receipt: flip `was_encrypted = true`, re-sign, re-record
the chain head. This is a *post-hoc augmentation* of (1) or (2)
rather than a fourth builder.

**The atomic paths construct NO receipt at all.**
`execute_atomic_sovereign` (executor.rs:12319) returns
`Result<Vec<[u8; 32]>, AtomicTurnError>`; `execute_mixed_atomic`
(executor.rs:12572) returns `Result<MixedAtomicResult, _>`. See §4.

### 2.4 What `receipt_hash()` binds (verbatim from `turn.rs:586-655`)

```text
dregg-receipt-v2
  turn_hash                                  (32)
  forest_hash                                (32)
  pre_state_hash                             (32)
  post_state_hash                            (32)
  timestamp (LE)                             (8)
  effects_hash                               (32)
  computrons_used (LE)                       (8)
  action_count (LE u64)                      (8)
  agent                                      (32)
  federation_id                              (32)
  previous_receipt_hash (presence + value)   (1+32 or 1)
  routing_directives.len() (LE)              (8) + per-rd hash      (32 each)
  introduction_exports.len() (LE)            (8) + per-ie absorb    (variable)
  derivation_records.len() (LE)              (8) + per-dr hash      (32 each)
  emitted_events.len() (LE)                  (8) + per-ev absorb    (variable)
  finality byte                              (1)
  was_encrypted byte                         (1)
```

Postcard is **not** used. The hash is a hand-rolled BLAKE3 absorb
with explicit length prefixes and presence bytes for every
`Option`. This is the right pattern (postcard's
encoding has historically had `Option`/default footguns), but it
means **every new field is a v3 bump**, and the v2 layer is now
crowded.

### 2.5 What `WitnessedReceipt` adds (`turn/src/witnessed_receipt.rs:243-264`)

```rust
pub struct WitnessedReceipt {
    pub receipt:             TurnReceipt,           // unchanged
    pub proof_bytes:         Vec<u8>,                // STARK proof
    pub public_inputs:       Vec<u32>,               // PI in canonical-BabyBear u32
    pub witness_bundle:      Option<WitnessBundle>,  // scope-2 material
    pub witness_hash:        [u8; 32],               // BLAKE3 of postcard(bundle), or [0;32]
    pub aggregate_membership:Option<AggregateMembership>, // γ.2 hook; always None v1
}

pub struct WitnessBundle {
    pub trace_rows:      Vec<Vec<u32>>,             // EFFECT_VM_WIDTH columns
    pub availability:    WitnessAvailability,        // Inline only in v1
    pub recursive_proof: Option<RecursiveProofVariant>, // Golden Vision compression
}

pub struct RecursiveProofVariant {
    pub proof_bytes:        Vec<u8>,
    pub public_inputs:      Vec<u32>,
    pub recursive_vk_hash:  [u8; 32],
}
```

`witness_hash` is BLAKE3 over postcard-encoded `WitnessBundle`. Note
that **the witness bundle is the only place in the entire receipt
architecture where postcard appears as the canonical encoding**
(see drift catalogue §9).

Crucial structural point: the `WitnessedReceipt` does not have its
*own* canonical hash. Its identity is `receipt.receipt_hash()`; the
witness side is only bound via the verifier's `check_receipt_pi_binding`
which cross-checks PI[TURN_HASH] and PI[PREVIOUS_RECEIPT_HASH]
against the receipt's authoritative fields (verifier/src/lib.rs:477).
There is no `witnessed_receipt_hash() = H(receipt_hash || proof_bytes
|| witness_hash)`. The implication: a `WitnessedReceipt` whose
`receipt` is identical to another's but with different `proof_bytes`
is the same receipt by `receipt.receipt_hash()`. Whether that's a
bug or a feature depends on whether you think `proof_bytes` is
metadata about a receipt or part of the receipt. See §9.

### 2.6 `FederationReceipt` / `FederationReceiptBody`
(`federation/src/receipt.rs:42`, `:123`)

The federation receipt's body is *almost a subset* of `TurnReceipt`
— it carries `turn_hash`, `block_height`, `block_hash`, `agent`,
`nonce`, `pre_state_hash`, `post_state_hash`, `effects_hash`,
`previous_receipt_hash`. It does NOT carry `routing_directives`,
`introduction_exports`, `derivation_records`, `emitted_events`,
`was_encrypted`, or `finality`. It DOES carry `block_height` and
`block_hash` (which `TurnReceipt` does not).

Built in exactly one place: `node/src/blocklace_sync.rs:2043`
(`build_federation_receipt`). It is built **from** an existing
`TurnReceipt` — lifting receipt fields into the body and adding the
block-level fields the federation knows. In production it carries a
single Ed25519 signature from the local node (the BLS aggregation
path exists in `with_threshold_qc` but the live blocklace flow goes
through `with_vote_signatures` with a one-element vector — the
aggregator runs out-of-band, see the comment at
`blocklace_sync.rs:2030-2042`).

Verifier: `FederationReceipt::verify` (`federation/src/receipt.rs:197`)
checks version, epoch match, federation_id derivation, and either
the BLS or per-voter QC over `body.body_hash()`. The `body_hash` is
domain-separated `"dregg-fed-receipt-body-v1"`.

### 2.7 The receipt verifiers — every consumer

| Verifier | Defined at | Checks |
|---|---|---|
| `verify_receipt_chain` | `turn/src/verify.rs:117` | empty-chain reject; genesis has prev_hash=None; per-step prev_hash matches prior receipt_hash; per-step pre_state matches prior post_state; all receipts same agent |
| `verify_receipt_chain_head` | `turn/src/verify.rs:183` | runs `verify_receipt_chain`, returns head's post_state_hash |
| `verify_receipt_extends` | `turn/src/verify.rs:192` | online single-step: agent match + prev_hash match + pre_state=prior.post_state |
| `verify_receipt_chain_with_keys` | `turn/src/verify.rs:245` | runs `verify_receipt_chain` + Ed25519 over `canonical_executor_signed_message` against any provided pubkey |
| `verify_via_receipt_chain` | `federation/src/types.rs:359` | wrapper: head state must equal expected (federation-exit verifiability path) |
| `verifier::replay_chain` | `verifier/src/lib.rs:392` | scope-2 chain: per-WR: STARK verify; `check_receipt_pi_binding` (T8/T11); witness_hash recomputed from inline bundle; trace re-runs `EffectVmAir::eval_constraints` over every row pair |
| `verifier::replay_chain_recursive` | `verifier/src/lib.rs:870` | as above but uses bundle's `recursive_proof` via `verify_recursive_proof_variant` instead of trace-replay |
| `verifier::check_receipt_pi_binding` | `verifier/src/lib.rs:477` | cross-binds proof PI[TURN_HASH_BASE..]==receipt.turn_hash, PI[PREVIOUS_RECEIPT_HASH_BASE..]==receipt.previous_receipt_hash, IS_AGENT_CELL==1, chain-walk invariant against `prev_receipt_hash` arg |
| `WitnessedReceipt::verify_bilateral_chain` | `turn/src/witnessed_receipt.rs:374` | γ.2 Phase 1: bilateral cross-cell consistency across a bundle of per-cell WRs sharing one turn |
| `FederationReceipt::verify` | `federation/src/receipt.rs:197` | version + epoch + federation_id derivation + QC check over body_hash |
| `verify_bridge_receipt` | `cell/src/note_bridge.rs:604` (per DESIGN doc) | single Ed25519 against caller-supplied trusted keys |

### 2.8 Verifier divergence summary

The TurnReceipt verifiers do not agree on what to check:

| Check | `verify_receipt_chain` | `verify_receipt_chain_with_keys` | `verifier::replay_chain` |
|---|---|---|---|
| Hash chain continuity | ✓ | ✓ | ✓ (in `check_receipt_pi_binding`) |
| pre/post state continuity | ✓ | ✓ | only implicitly (via PI cross-binding) |
| Agent consistency | ✓ | ✓ | not enforced (replay-chain doesn't gate on agent) |
| Executor signature | — | ✓ when present | — |
| STARK proof verify | — | — | ✓ |
| PI ↔ receipt cross-binding | — | — | ✓ |
| Trace constraint replay | — | — | ✓ (or recursive variant) |
| Witness-hash recomputation | — | — | ✓ |
| Genesis prev_hash=None | ✓ | ✓ | implicit |
| Same-federation_id (cross-fed replay) | — | — | — |

Observation: a chain that passes `verify_receipt_chain` might **fail**
`verifier::replay_chain` (PI tampered, witness bundle missing,
STARK invalid). A chain that passes `replay_chain` does *not* check
that all receipts share the same agent (a deliberate mixed-agent
chain would pass `replay_chain` but fail `verify_receipt_chain`).
Neither checks `federation_id` consistency, even though
`receipt.federation_id` is bound into `receipt_hash`. This is drift
— see §9.

### 2.9 The third hash view: `FederationReceiptBody::body_hash`

```text
new_derive_key("dregg-fed-receipt-body-v1")
  turn_hash || block_height || block_hash || agent || nonce
  || pre_state_hash || post_state_hash || effects_hash
  || prev_hash (presence + value)
```

This is the **third** canonical hash over receipt content
(after `Turn::hash` v3 and `TurnReceipt::receipt_hash` v2). Its
relationship to the others is:

- The `Turn::hash` is computed by the executor on the input turn;
  bound into `receipt_hash` and `body_hash` as `turn_hash`.
- The `TurnReceipt::receipt_hash` is what the executor signs (well,
  signs a *narrow projection* of) and what subsequent turns refer to
  via `previous_receipt_hash`.
- The `FederationReceiptBody::body_hash` is what the federation's BFT
  quorum signs; it covers a *strict subset* of `receipt_hash` plus
  block-level facts (`block_hash`, `block_height`) the executor did
  not know.

**There is no commitment that ties `receipt_hash` and `body_hash`
together.** A federation receipt covers `turn_hash`, `pre/post`, and
`effects_hash` — but if the executor's `TurnReceipt.routing_directives`
or `derivation_records` were tampered with, the federation receipt
would not detect it. A holder of both the `TurnReceipt` and the
`FederationReceipt` for the same turn would have to trust the
executor for the "extras" not in the body. See §9.

---

## §3. Receipt chain semantics — extension, fork, merge, pruning

### 3.1 Chain extension — what's enforced

The chain link is `TurnReceipt.previous_receipt_hash:
Option<[u8; 32]>`. Enforcement points:

- **Write-time (executor)** at executor.rs:4324:
  `self.check_previous_receipt_hash(&turn.agent, turn.previous_receipt_hash)`
  rejects a turn whose claimed prev_hash does not equal the executor's
  per-agent stored head (or `None` for first turn).
- **Auto-fill (pipeline/composer)** at executor.rs:11826 and 12033:
  if `resolved_turn.previous_receipt_hash.is_none()`, the executor
  auto-populates it from `get_last_receipt_hash(&resolved_turn.agent)`.
  This is convenient but means submitters can omit the field and let
  the executor fill it in.
- **Read-time (off-chain)** at verify.rs:117 — every consecutive
  pair must have `next.previous_receipt_hash == Some(prev.receipt_hash())`.
- **Read-time (scope-2 replay)** at verifier/src/lib.rs:477 — the
  PI must commit to `prev_receipt_hash` *and* the chain-walk
  invariant against the prior entry's hash must hold.

The per-agent head is held in the executor at executor.rs:849
(`last_receipt_hash: Mutex<HashMap<CellId, [u8; 32]>>`). It is
*in-memory state*: the chain head is not derived from the ledger
itself, it's an auxiliary index. `set_last_receipt_hash` (executor.rs:1356)
is provided for state recovery on restart. See §8.

### 3.2 Fork — where chains can diverge

The chain is **defined to be linear per agent**: each agent has
exactly one chain. Mechanisms that could fork it:

- **Executor restart without re-seeding `last_receipt_hash`.** If a
  new executor accepts a turn from agent A with `previous_receipt_hash:
  None` (a claimed genesis), and the agent actually had history, the
  new executor's chain forks from the old. The check at
  `check_previous_receipt_hash` only rejects when `previous_receipt_hash
  != stored_head` — if the executor has no stored head (post-restart,
  not seeded), it accepts anything. **This is a fork vector.**
  Documented at executor.rs:1350 ("Without seeding, the first turn
  from an agent with pre-existing history would be rejected as
  `ReceiptChainMismatch`") — but the rejection is conditional on
  the agent having pre-existing turns *that the executor knows about*.
  If the executor's memory is fresh and the agent claims genesis, no
  rejection.
- **Byzantine executor / federation.** Nothing in the receipt
  structure prevents two executors from each issuing a different
  receipt R₁, R₂ for the same `(agent, nonce, prev_hash)`. The
  federation-level consensus is what resolves this; at the receipt
  layer alone, both look valid.
- **Cross-federation.** The `federation_id` binding (added in
  receipt v2) prevents a receipt from federation A from satisfying a
  TurnExecuted condition targeting federation B. But there is no
  *cross-chain link* — agent A's chain in federation X and agent A's
  chain in federation Y (if both federations recognize the same
  `CellId`) are entirely independent. There is no protocol-level
  shape for "agent A migrated from X to Y; here's the bridging link."

### 3.3 Merge — cross-cell joins

There is no cross-cell receipt-chain merge primitive. Receipts are
per-agent (the `agent` field selects the chain). When a turn touches
many cells, *one* receipt is emitted; that receipt records
`emitted_events` and `derivation_records` per cell, but the *receipt
chain* belongs to `turn.agent`, not to every cell the turn touched.

This means cells that are passive recipients of effects (e.g., a
target cell whose balance is decremented by a Transfer the agent
initiated) have **no receipt-chain participation** of their own.
Their state evolves silently; the audit trail lives in the
*initiator's* chain. A holder of just the target cell's state and
the federation-attested root cannot reconstruct the target's history
without consulting other agents' receipt chains.

Per `PROTOCOL-CATEGORICAL-ANALYSIS.md §4.4`, the cross-cell
recursive receipt (`CrossCellRecursiveReceipt`) is "landing" via
γ.2 Phase 2 (Joint Bilateral Aggregation AIR) — not yet shipped.
Today's mechanism is `WitnessedReceipt::verify_bilateral_chain`
(turn/src/witnessed_receipt.rs:374) which is a γ.2 Phase 1 *off-AIR*
consistency check across a bundle of per-cell WRs from the same
turn. It verifies bilateral edge counts and accumulator roots
against the turn's call_forest; it does not produce a *receipt*, it
verifies a *bundle*.

### 3.4 Pruning — `ReceiptArchive` and its incomplete wiring

`Effect::ReceiptArchive` (`turn/src/action.rs:1080`) carries an
`ArchivalAttestation` (`cell/src/lifecycle.rs:248`). On apply
(executor.rs:10606), it:

1. checks `checkpoint.cell_id == action.target`
2. checks `checkpoint.archive_end_height == prefix_end_height`
3. rejects `prefix_end_height > self.block_height`
4. calls `c.archive(checkpoint)` — which transitions the cell's
   `CellLifecycle` to `Archived { checkpoint_hash, archived_through }`
   (cell/src/lifecycle.rs:73-82, cell/src/cell.rs:474).

**The archive effect mutates the cell's lifecycle but does NOT
touch the receipt-chain head.** Critically:

- The `ArchivalAttestation` includes `archive_terminal_receipt_hash`
  (`cell/src/lifecycle.rs:262`). This is what the live tail's
  `previous_receipt_hash` is supposed to point at after the archive
  — but **the executor does not enforce this binding**. There is no
  code that says "after archive, the per-agent `last_receipt_hash`
  must equal `archive_terminal_receipt_hash`." The two are
  independent objects.
- The `archive_terminal_commitment` is the post-state at the cutover
  height. There is no enforcement that the cell's current
  `state_commitment()` equals it — although in practice they should
  match if the archive is truthful.
- The `archive_blob_hash` is opaque — it commits to off-chain bytes;
  no on-chain verifier consults it.

A verifier confronted with `CellLifecycle::Archived { checkpoint_hash,
archived_through }` learns the checkpoint exists but cannot
distinguish "I see the checkpoint, the prefix it summarizes is
authentic" from "I see a checkpoint but its claim about the prefix
is unverified". The `ArchivalAttestation::validate()`
(cell/src/lifecycle.rs:283) only checks structural invariants
(start≤end, non-zero blob/terminal hash). There is no signature on
the attestation, no federation co-attestation, no link to a
particular `AttestedRoot`. The attestation is *self-asserted by the
cell owner*.

### 3.5 Pruning — when a parent cell is destroyed

`CellLifecycle::Destroyed { death_certificate_hash, destroyed_at }`
(cell/src/lifecycle.rs:63). The `DeathCertificate`
(cell/src/lifecycle.rs:147) carries `last_receipt_hash`,
`final_state_commitment`, `destroyed_at_height`, and `reason`. So
"the cell's chain terminates here" is structurally recordable.

But `Effect::CellDestroy` (action.rs ~1080) — does *destruction of
a parent cell* invalidate child receipts? No: receipts belong to
the *initiator* (`agent`), not to a hierarchical parent. A spawned
cell whose creator is destroyed *retains* its own state and its own
receipt chain (the destruction doesn't propagate). The
`DeathCertificate` says "this cell stops here" only for the
destroyed cell itself.

A verifier reconstructing state from the receipt stream after
parent-destruction sees: parent ends at receipt H. Child still
produces receipts after H. The child's `derivation_records`
(received at spawn time) point at parent's cap; the parent's
absence makes those derivation records "dangling pointers" from a
reconstruction perspective — the chain still verifies, but you
can't re-derive *why* the child has the authority it does without
reaching back into the parent's pre-destruction history.

This is *fine* — caps are content-addressed; once granted, the
derivation record is sufficient. But it does mean that the
persistence stream's "state is derivable from the stream" property
requires keeping the parent's pre-destruction receipts available
forever (or archiving them with an attestation that the verifier
trusts).

### 3.6 What's enforced vs. what's convention

| Invariant | Enforcement | Where |
|---|---|---|
| Chain extension by hash | Code | executor.rs:4324, verify.rs:147 |
| State continuity (pre==prior.post) | Code | verify.rs:167 |
| Same-agent across chain | Code | verify.rs:138 |
| Same-federation across chain | Convention | (no verifier check; federation_id IS in receipt_hash) |
| `executor_signature` valid when present | Code | verify.rs:265 |
| `executor_signature` covers all soundness-meaningful fields | Convention (broken) | turn.rs:686-698 covers a narrow subset; doc says this is "deliberate" |
| `was_encrypted` truthfully reflects path | Code (only via receipt_hash, not signature) | turn.rs:653 |
| Witness bundle hash matches `witness_hash` | Code (off-chain) | verifier/src/lib.rs:613 |
| Witness bundle PI matches receipt | Code (off-chain) | verifier/src/lib.rs:477 |
| `previous_receipt_hash` matches archive terminal | Convention (no code) | lifecycle.rs:262 documents the intent; no enforcement |
| `FederationReceipt.body_hash` matches `TurnReceipt.receipt_hash`-derived facts | Convention (no cross-check) | (no verifier links them) |

---

## §4. The atomic-path gap — design for receipts in atomic execution

### 4.1 What's missing today

`execute_atomic_sovereign` (executor.rs:12319-12557) returns
`Result<Vec<[u8; 32]>, AtomicTurnError>` — only the new cell
commitments. `execute_mixed_atomic` (executor.rs:12572-12921)
returns `Result<MixedAtomicResult, AtomicTurnError>` — commitments
+ sovereign deltas + hosted deltas. **Neither builds a `TurnReceipt`.**

The implications:

- The agent's receipt chain has a *hole* at every atomic execution.
  The next regular turn from the agent will have
  `previous_receipt_hash = Some(stale_head)` because the atomic path
  does not call `record_receipt_hash`.
- `verify_receipt_chain` cannot detect the gap — it has nothing to
  verify because no receipt was emitted.
- A federation reconstructing state from the receipt stream alone
  *cannot recover the sovereign commitment updates the atomic path
  applied*. The state derived from the stream diverges from the
  actual ledger state.
- The "persistence-layer" property collapses: state on disk is *not*
  derivable from the receipt stream when atomic paths are used.

### 4.2 What an atomic receipt should bind

A `TurnReceipt` for `execute_atomic_sovereign` should commit to:

- `turn_hash` — hash of the `AtomicSovereignTurn` (analogous to
  `Turn::hash`)
- `pre_state_hash` / `post_state_hash` — `ledger.root()` before/after
- `agent`, `nonce`, `fee`, `previous_receipt_hash` — chain participation
- An `effects_hash` whose preimage enumerates *the atomic entries
  applied*. Each entry: `(cell_id, old_commitment, new_commitment,
  vk_hash_used, proven_balance_delta)`. This gives a verifier
  reading the receipt stream the cell-level state-transition
  evidence.
- A per-cell VK commitment (the `vk_set_commitment` from
  EXECUTOR-VK-AUDIT §6.1) so the receipt is VK-self-describing.
- `was_encrypted = false`, `finality = Final` like other paths.

For `execute_mixed_atomic`, additionally:

- An `effects_hash` covering hosted effects in canonical order.
- Routing/introduction/derivation records collected from the hosted
  side.

### 4.3 Smallest change to make the paths receipt-producing

1. Refactor `execute_atomic_sovereign` to return
   `Result<(TurnReceipt, Vec<[u8; 32]>), AtomicTurnError>`. The
   commitments stay in the result tuple for back-compat with current
   callers; the receipt is new.
2. Build the receipt at commit-time (after step 4 in the existing
   flow): compose `effects_hash` from the per-entry
   `(cell_id, old, new, vk_hash, delta)` tuples; pull
   `pre_state_hash` from a snapshot taken at function entry
   (currently not captured — would need to add a `ledger.root()`
   call before any mutation).
3. Call `record_receipt_hash(turn.agent, receipt.receipt_hash())`
   to extend the per-agent chain head.
4. Call `maybe_sign_receipt` to populate `executor_signature`.

For `execute_mixed_atomic`, same shape but the receipt absorbs both
sovereign and hosted effects.

### 4.4 Subtleties

- **Atomicity of the chain-head update.** The chain head must be
  updated **only** if the entire atomic turn commits. The current
  code structure makes this easy (head update at the end, after all
  rollback paths have been exhausted). The only risk is a panic
  mid-commit; the existing classical path has the same risk.
- **The `was_encrypted` flag.** Atomic paths don't have an
  encrypted-turn analog today, but if `apply_encrypted_atomic` ever
  lands, the same post-hoc flip pattern as
  `apply_encrypted_turn`/`execute_encrypted_turn` should apply.
- **Sovereign-witness sequence binding.** The atomic path increments
  per-cell sovereign witness sequences via
  `ledger.update_sovereign_commitment`. Like the classical path,
  these sequence bumps should be reflected in the receipt's
  `derivation_records` or a new field. Today neither path includes
  them explicitly.

---

## §5. The encrypted-turn coverage gap

### 5.1 What is and isn't bound today

In `receipt_hash` (✓ bound):
- `was_encrypted` byte (turn.rs:653)

In `canonical_executor_signed_message` (✗ NOT bound):
- `was_encrypted`
- `finality`
- `effects_hash`
- `routing_directives` / `derivation_records` / `emitted_events`
- `previous_receipt_hash`

Neither place binds:
- `EncryptedTurn.turn_commitment` (the federation's
  ordering-commitment for the envelope, encrypted.rs:71)
- `EncryptedTurn.ephemeral_public` (the X25519 sender DH key)
- `EncryptedTurn.nonce` (the ChaCha20-Poly1305 12-byte nonce)
- The executor's `sealer_secret` / public key (the identity that
  could decrypt this envelope)
- A per-encrypted-turn ordering position (which bucket / submitted_at
  index)

### 5.2 What this lets a verifier deduce — and what it doesn't

A holder of a receipt with `was_encrypted = true`:
- Knows the receipt came through the privacy path.
- Knows the inner turn's `turn_hash` (because the receipt commits
  to it).
- *Cannot* prove "this receipt corresponds to *that specific
  envelope* the federation ordered." There is no link between the
  envelope's `turn_commitment` (a BLAKE3 over plaintext bytes,
  encrypted.rs:71) and the receipt. The federation's commitment to
  ordering an envelope is unfalsifiable but unprovable in the
  receipt direction.
- *Cannot* tell which executor / sealer-keypair processed it.

The deep audit (EXECUTOR-VK-AUDIT §4.1 / §5.9) frames this as: the
encrypted-turn ordering commitment is *not* bound back into the
receipt. A federation can be honest about ordering envelopes *and*
the receipt chain can be honest about state transitions, but a third
party cannot prove the two streams correspond at any specific point.

### 5.3 What should be bound

- `EncryptedTurn.turn_commitment` → a new
  `TurnReceipt.encrypted_envelope_commitment: Option<[u8; 32]>`
  field, populated when `was_encrypted` is true. This is the
  EXECUTOR-VK-AUDIT §6.6 fix.
- The executor's sealer pubkey (the X25519 public key whose secret
  decrypted this envelope). Closes "which executor processed this?"
- The ordering position (bucket index + submission time) the
  envelope occupied. This makes the receipt a verifiable witness of
  "this envelope was scheduled here" — a property the federation
  has but does not expose.
- Bump `canonical_executor_signed_message` to v3 to include
  `was_encrypted`, `finality`, `effects_hash`, and the new
  envelope-commitment field. A signature-only verifier currently
  sees a strictly weaker statement; per §2.2 above this is now
  a known gap.

### 5.4 Subtlety: re-sign on the bit-flip is correct but fragile

At executor.rs:1208 and executor.rs:1285, after the encrypted path
flips `was_encrypted = true`, the executor re-signs the receipt
because `receipt_hash` changed. This is *correct* given the current
signing message (which doesn't include `was_encrypted`, so the
signature itself is unchanged — only the binding to
`receipt_hash()` is rebuilt). But it is fragile: if a future change
adds a field to the signing message that *does* depend on the
encrypted-path bit, the order of operations (flip then sign) becomes
load-bearing in a non-obvious way. Better: derive the encrypted-ness
from a primary source (e.g., a `path: ExecutionPath` enum on the
receipt) and have all the bound bits computed deterministically from
it.

---

## §6. Recursive-scope receipts — outer-inner commitment relationship

### 6.1 The two recursive paths today

(a) **Single-cell recursive compression** via
`WitnessBundle.recursive_proof: Option<RecursiveProofVariant>`
(turn/src/witnessed_receipt.rs:121, 134-148). A producer who has the
inline trace can additionally produce a recursive STARK proof
attesting that the inline trace satisfied the AIR. The two replay
modes are equivalent in soundness *for the same trace*.

(b) **Chain-IVC** via `dregg_circuit::ivc` and the
`IvcBuilder`-driven `append_receipt` hook in
`sdk/src/cipherclerk.rs:1800` (cclerk-local; not federation-side).
This folds successive receipts' state transitions into a single
running IVC commitment. The fold is *best-effort* — if it fails the
receipt is still appended (cipherclerk.rs:1829).

### 6.2 Outer-inner commitment relationship audit

For (a):
- **Outer commits to inner via PI cross-binding.**
  `verify_recursive_proof_variant`
  (circuit/src/recursive_witness_bundle.rs:354) checks
  `RecursiveProofVariant.public_inputs == TurnReceipt`-derived PI
  (line 379-395, when `expected_pi_u32` is supplied). The verifier
  caller is supposed to pass the receipt's authoritative PI; if
  they pass `None`, the cross-binding is skipped.
- **Coverage gap.** The recursive proof's inner AIR is
  `EffectVmShapeAir`, a constraint-subset of `EffectVmAir`
  (AIR-SOUNDNESS-AUDIT §2.G). A trace accepted by the shape AIR may
  violate non-structural constraints of the full AIR. So the
  recursive variant's "I attest the inner proof is sound" is a
  *narrower* claim than "I attest the inline-trace replay would
  pass." Silver Vision is OK because the inline trace remains the
  authoritative scope-2 check; Golden Vision (drop the trace, rely
  on recursive proof) is **not yet soundness-equivalent**.
- **The outer does NOT commit to the receipt's `receipt_hash`.**
  The cross-binding is at the *PI* level, not the receipt-hash
  level. If `expected_pi_u32` is omitted, the recursive variant is
  free-floating: it attests "some trace exists that satisfies the
  shape AIR with these PI," with no link to which receipt produced
  the trace. The current verifier flow always passes the receipt's
  PI, so this is OK in practice; but it's a contract that lives in
  the verifier, not in the variant itself.

For (b):
- The IVC state is **cclerk-local**. There is no
  `TurnReceipt.ivc_commitment` field; the running IVC commitment
  isn't published anywhere on-chain. Two honest cipherclerks running the
  same chain compute the same IVC commitment, but no verifier
  consults it.
- On `append_receipt`, the cclerk *mutates* `receipt.previous_receipt_hash`
  to point at its own chain head (cipherclerk.rs:1797). If the
  cipherclerk's chain has diverged from the executor's (e.g., cclerk
  missed a receipt), the appended receipt's hash will not match
  what the executor recorded. This is a **drift vector** worth
  calling out (§9).

### 6.3 What a sound recursive-scope receipt should commit to

An outer `RecursiveReceipt` (single-cell) should bind:
- inner `WitnessedReceipt.receipt.receipt_hash()` — the canonical
  identity of the receipt being attested
- inner `WitnessedReceipt.witness_hash` — the bundle identity
- inner `RecursiveProofVariant.recursive_vk_hash` — which recursive
  VK was used
- the recursive proof bytes

Concretely:
```rust
pub struct RecursiveReceipt {
    pub inner_receipt_hash: [u8; 32],
    pub inner_witness_hash: [u8; 32],
    pub recursive_vk_hash:  [u8; 32],
    pub proof_bytes:        Vec<u8>,
}
```

This object has its own canonical hash and is independently
verifiable: "I am a recursive attestation of receipt R₁'s scope-2
soundness under VK V." Today there is no such object — the
recursive proof is opaque-bundled into `WitnessBundle.recursive_proof`
and its identity is the bundle's identity, not the proof's own.

For cross-cell recursion (the γ.2 Phase 2 "Joint Bilateral
Aggregation"), per `PROTOCOL-CATEGORICAL-ANALYSIS.md §4.4`:
```rust
pub struct CrossCellRecursiveReceipt {
    pub pair: (CellId, CellId),
    pub receipts: (WitnessedReceipt, WitnessedReceipt),
    pub aggregate_proof: Vec<u8>,
    pub aggregate_pis: Vec<u32>,
}
```
The outer proof binds both inner `receipt_hash`es and the bilateral
edge they share. This is in flight; the Phase 1 off-AIR check
(`WitnessedReceipt::verify_bilateral_chain`) is the structural
precursor.

---

## §7. ReceiptArchive design — how the new lifecycle work fits in

### 7.1 What landed

- `CellLifecycle::Archived { checkpoint_hash, archived_through }`
  (`cell/src/lifecycle.rs:73-82`).
- `ArchivalAttestation` struct with
  `(cell_id, archive_start_height, archive_end_height, archive_blob_hash,
   archive_terminal_commitment, archive_terminal_receipt_hash)`
  (lifecycle.rs:247-265).
- `ArchivalAttestation::checkpoint_hash()` —
  domain-separated BLAKE3 absorb of every field (lifecycle.rs:270).
- `ArchivalAttestation::validate()` — structural invariants
  (lifecycle.rs:283).
- `Cell::archive(checkpoint)` — lifecycle transition method
  (cell/src/cell.rs:474).
- `Effect::ReceiptArchive { prefix_end_height, checkpoint }`
  (turn/src/action.rs:1080).
- Executor apply-handler at executor.rs:10606: validates `cell_id`
  match, `prefix_end_height == archive_end_height`, `prefix_end_height
  <= block_height`; calls `c.archive(checkpoint)`; journals lifecycle.

### 7.2 What's missing

1. **Federation co-attestation.** The attestation is *self-asserted*:
   the cell owner asserts the archive is canonical, but no quorum
   signs it. The `ReceiptArchive` effect runs through the standard
   turn pipeline, so the *turn* is federation-attested (via the
   resulting `TurnReceipt`), but the `ArchivalAttestation` itself is
   not separately signed. This conflates "the federation ran this
   turn" with "the federation accepts the archive's claim about
   off-chain content."
2. **No binding between `archive_terminal_receipt_hash` and the
   chain head.** Per §3.4, the executor does not enforce that the
   per-agent `last_receipt_hash` equals `archive_terminal_receipt_hash`
   after the archive. A malicious cell owner can submit an
   `ArchivalAttestation` whose terminal hash is unrelated to the
   actual chain head, and the executor will accept it. Subsequent
   turns will continue extending the *actual* chain head; the
   attestation's terminal hash will be a dangling pointer that no
   live chain link references.
3. **No verifier-facing API for "is this archive checkpoint
   authentic?"** A verifier presented with `CellLifecycle::Archived
   { checkpoint_hash, .. }` can recompute `checkpoint_hash` from a
   supplied `ArchivalAttestation` (by calling `checkpoint_hash()`),
   but has no way to verify that the off-chain blob exists or its
   hash matches `archive_blob_hash`.
4. **No retention policy.** Per `HOUYHNHNM-COMPARISON.md §5.1`,
   real deployments will need
   `RetentionPolicy::{KeepForever, KeepWindow(epochs),
   KeepAttestedRootsOnly}` declarations. Today every federation
   member retains everything implicitly; archiving is a per-cell
   override with no per-operator dimension.

### 7.3 The "history prefix → checkpoint" relationship — what it actually means

After `Effect::ReceiptArchive` commits with attestation A on cell C:
- C's lifecycle is `Archived { checkpoint_hash: A.checkpoint_hash(),
  archived_through: A.archive_end_height }`.
- The off-chain blob hash `A.archive_blob_hash` commits to the
  *full prefix* of C's chain through `A.archive_end_height`.
- The next live receipt for C (or for any agent whose turn touches
  C) should structurally extend from `A.archive_terminal_receipt_hash`
  — but the executor doesn't enforce this. A verifier walking the
  live tail finds a chain head, then sees the archive's terminal
  hash and the live head are *both* claimed to be "the last receipt
  before / at the archive" with no mechanism to confirm they
  coincide.

### 7.4 What a verifier needs to distinguish "see-the-checkpoint" from "trust-the-checkpoint"

The categorical distinction in the brief is real: a verifier should
be able to say either:
- "I see the checkpoint AND the prefix it summarizes is authentic"
  (the off-chain blob has been fetched, its hash matches
  `archive_blob_hash`, the prefix is itself a valid receipt chain
  whose terminal hash matches `archive_terminal_receipt_hash`, the
  terminal commitment matches `archive_terminal_commitment`).
- "I see the checkpoint but its claim about the prefix is
  unverified" (the verifier has not fetched the blob; they trust
  the federation co-attestation, or they trust the cell owner's
  self-assertion, or they trust nothing — and the verifier should
  *say* which).

Today there is no API for either. A future `ReceiptArchive`-aware
verifier would:
1. Take `Cell` + optional off-chain blob bytes.
2. If blob present: BLAKE3-hash it, compare to
   `attestation.archive_blob_hash`; parse it as a
   `Vec<TurnReceipt>` and `verify_receipt_chain` it; check head
   `receipt_hash` matches `archive_terminal_receipt_hash` and
   head `post_state_hash` matches `archive_terminal_commitment`.
   Verdict: "Archive verified."
3. If blob absent: structural-only — `attestation.validate()` +
   `attestation.checkpoint_hash() == cell.lifecycle.checkpoint_hash`.
   Verdict: "Archive structurally consistent; prefix not verified."

Neither verdict path exists today.

---

## §8. The reconstruction question — can dregg actually rebuild state from receipts alone?

### 8.1 What's covered by the receipt stream

A receipt stream + genesis lets you reconstruct:
- **Every cell's ledger state** as of the chain head, *if* every
  turn that touched the cell went through `execute()` (the classical
  / proof-carrying path). `pre_state_hash` / `post_state_hash`
  commits to `ledger.root()` at each step, but the root is BLAKE3
  over postcard-encoded per-cell state — so the receipt commits to
  the *root*, not the per-cell deltas. Reconstruction works by
  replaying the effects (recorded in `effects_hash` preimage —
  except: the effects_hash is the BLAKE3 of the runtime sequence,
  and the preimage itself is not in the receipt). So
  *the effects themselves are not in the receipt*; they have to be
  re-derived from the original `Turn::call_forest` (which the
  receipt commits to via `forest_hash`).
- **Every cell's nullifier set** *if* every NoteSpend went through
  `execute()` (it does, via the journal at journal.rs:240).
- **Every cell's capability set** *if* every Grant/Revoke went through
  `execute()` and `derivation_records` was correctly emitted.
- **Every cell's lifecycle state** *if* every Seal/Unseal/Destroy/
  Archive went through `execute()`.
- **Every cell's sovereign-witness sequence** *if* every sovereign
  witness was bumped through `execute()`.

### 8.2 What's NOT covered by the receipt stream

1. **Atomic-path mutations.** Per §4, `execute_atomic_sovereign`
   and `execute_mixed_atomic` emit no receipt. The sovereign
   commitments they update are *not* derivable from the receipt
   stream. **A federation that uses atomic paths cannot pass the
   §1.2 reconstruction test.**
2. **In-memory cap handles / promises.** CapTP `SturdyRef`s,
   live promise pipelining state, `AnswerSlot` tables, three-party
   handoff certificates — these are *transport-layer* state that
   lives in the captp session and never enters the ledger or the
   receipt. A reconstructed node has no in-flight promises.
   *(This is correct — transport state should not persist.)*
3. **Cell-program ephemeral state.** Sovereign cells hold internal
   state behind their state commitment; the commitment is
   reconstructible from the chain (the per-turn `new_commitment` is
   in `execution_proof_new_commitment` and bound into `turn.hash`),
   but the *internal structure* of the sovereign state is not.
   Reconstructing the cell's internal slots requires the cell owner
   to supply the pre-image (the `SovereignCellWitness.cell_state`
   carries this at proof-time, but is not in the receipt). *(This
   is intentional — sovereign cells hide their internals.)*
4. **Encrypted-turn plaintexts.** The receipt records `was_encrypted
   = true` and the inner `turn_hash`, but the inner turn body is
   not in the receipt. A reconstructor sees "a turn happened, its
   hash was H" without knowing what the effects were. *(This is
   correct for an external reconstructor; the cell owner can keep
   the plaintext locally.)*
5. **Block-level federation facts.** `block_height`, `block_hash`,
   `finality_round`, `blocklace_block_id` are in `FederationReceipt`
   but NOT in `TurnReceipt`. A receipt-stream reconstructor sees
   the turn ordering but not the federation's block boundaries. The
   federation's `AttestedRoot` ties these together but is a separate
   stream.
6. **Cross-cell consistency witnesses (γ.2).** Bilateral edge
   counts, accumulator roots — recorded in PI but not bound into
   `receipt_hash`. A reconstructor cannot tell from the receipts
   alone whether γ.2 cross-cell consistency was checked.
7. **Witness bundles.** A `TurnReceipt` (not `WitnessedReceipt`) has
   no trace data. Replaying `EffectVmAir` requires the bundle,
   which is stored in `WitnessedReceipt` — a separate, opt-in,
   typically prover-local shape. The persistence claim implicitly
   means "WitnessedReceipt chain" not "TurnReceipt chain"; but most
   of the codebase (executor, cclerk, federation, blocklace) operates
   on bare `TurnReceipt`. The `WitnessedReceipt` lift happens only
   at the prove site (node/src/mcp.rs) and is opt-in per-turn.
8. **Ledger root preimages.** The receipt commits to `pre_state_hash`
   and `post_state_hash`, both `Ledger.root()` outputs. The root is
   BLAKE3 over canonical_ledger_root (blocklace_sync.rs:2093) which
   is BLAKE3 over postcard(cell.state) per-cell sorted by cell_id.
   To reconstruct state, you need either (a) a starting ledger and
   the ability to apply each turn's effects (re-derivable from
   `forest_hash` preimage = the original `Turn`) or (b) Merkle-style
   inclusion proofs per cell. Today only (a) is supported. A
   verifier reconstructing from scratch must hold the original
   `Turn` for every receipt — the receipt alone is insufficient.

### 8.3 Verdict on §1.2's reconstruction test

**Partial pass.** Under the assumption that:
- atomic paths are not used (false today)
- the receipt stream is accompanied by the original `Turn` for each
  receipt (the receipt commits to `turn_hash` and `forest_hash`, not
  to the forest body itself)
- witness bundles are retained for scope-2 verification of sovereign
  transitions
- federation `AttestedRoot`s are retained for block-level binding
- the `ArchivalAttestation` enforcement gap (§7) is closed so
  archived prefixes link cleanly to live tails

...the WitnessedReceipt chain *is* dregg's persistence layer for
hosted-cell state. For sovereign-cell internal state and for the
atomic-path commitments, it is not yet.

### 8.4 The "extra streams" problem

The reconstructor needs at least four streams:
1. The `TurnReceipt` chain per agent.
2. The `Turn` bodies (the receipt only commits to their hashes).
3. The `WitnessedReceipt` bundles (for sovereign / proof-carrying
   transitions, to recover state-commitment preimages).
4. The federation's `AttestedRoot` stream (for block-level finality).

These are *not* unified. The "single persistence layer" framing is
aspirational; the *current* design has three or four parallel
streams that compose only by convention. See §10.

---

## §9. Drift catalogue — where two paths build / verify receipts differently

### 9.1 Two construction sites for `TurnReceipt`

| Field | Classical path (4898) | Proof-carrying path (4438) |
|---|---|---|
| `effects_hash` | `compute_effects_hash(&all_effects_hashes)` | `compute_effects_hash(&[])` — empty! |
| `computrons_used` | actual cost | 0 |
| `action_count` | `turn.call_forest.action_count()` | 0 |
| `routing_directives` | collected from forest | `vec![]` |
| `introduction_exports` | collected from forest | `vec![]` |
| `derivation_records` | collected from forest | `vec![]` |
| `emitted_events` | collected from journal | `vec![]` |
| `finality` | `Final` | `Final` |
| `was_encrypted` | `false` (encrypted path flips post-hoc) | `false` |
| `executor_signature` | `maybe_sign_receipt(...)` | `maybe_sign_receipt(...)` |

The two paths agree on *structure* but disagree on *content fidelity*:
the proof-carrying path's receipt is structurally a "stub receipt"
whose fields claim less than the proof attested. A long-running
verifier reading both kinds of receipts cannot tell that the proof
attested to a non-trivial transition while the receipt declares zero
actions. This is EXECUTOR-VK-AUDIT §2.2.

### 9.2 Verifier divergence (see §2.8 table)

`verify_receipt_chain` and `verifier::replay_chain` enforce different
sets of invariants. Neither subsumes the other.

### 9.3 Two `receipt_hash` views per receipt

`receipt_hash()` covers 18 fields. `canonical_executor_signed_message`
covers 6. A signature-only verifier and a receipt-hash verifier
form *strictly different trust assumptions*.

### 9.4 Three-way encoding divergence

| Object | Hash encoding |
|---|---|
| `Turn::hash` | hand-rolled BLAKE3 absorb, version `dregg-turn-v3` |
| `TurnReceipt::receipt_hash` | hand-rolled BLAKE3 absorb, version `dregg-receipt-v2` |
| `FederationReceiptBody::body_hash` | hand-rolled BLAKE3 via `new_derive_key("dregg-fed-receipt-body-v1")` |
| `WitnessBundle::witness_hash` | **postcard** + BLAKE3 |
| `ArchivalAttestation::checkpoint_hash` | hand-rolled BLAKE3 via `new_derive_key("dregg-cell:archival-attestation v1")` |
| `DeathCertificate::certificate_hash` | hand-rolled BLAKE3 via `new_derive_key("dregg-cell:death-certificate v1")` |
| `AttestedRoot::signing_message` | hand-rolled `Vec<u8>` build (no BLAKE3 — the signature scheme hashes) |

Two patterns mixed: `Hasher::new()` + manual domain tag (Turn, Receipt)
vs. `Hasher::new_derive_key(label)` (Federation body, Archive,
DeathCert). And one outlier (`WitnessBundle`) uses postcard.

### 9.5 Cipherclerk rewriting `previous_receipt_hash`

`cipherclerk.rs:1797`:
```rust
receipt.previous_receipt_hash = self.receipt_chain.last().map(|r| r.receipt_hash());
```

The cclerk **overwrites** the receipt's `previous_receipt_hash` to
the cipherclerk's view of the chain head before storing it. If the
executor and cclerk disagree (network partition, cclerk missed a
turn), the cipherclerk's stored receipt has a *different* `receipt_hash`
than the executor's. The cipherclerk's chain then diverges from the
federation's. A verifier reading the cipherclerk's chain sees a valid
chain that is *not* the federation's chain.

The intent is recovery from out-of-order delivery, but the mechanism
is silent rewriting. A stricter design: reject append-receipt if the
hash mismatch is non-trivial, or surface a divergence signal.

### 9.6 Auto-fill of `previous_receipt_hash` in the executor

executor.rs:11832 / 12036: if a submitter omits `previous_receipt_hash`,
the executor auto-fills from its `last_receipt_hash` map. Combined
with §9.5's cclerk rewrite, the chain head is determined by
*whichever side has fresher information*. This is not necessarily
unsound, but the rule "the submitter signs over the actual chain
head" is bent — the auto-fill happens after sign time. (Cipherclerk
signature compatibility is preserved because `Turn::hash` covers
`previous_receipt_hash` after auto-fill, but the cipherclerk's signed
turn hash from `compute_turn_bytes` may not match — this is a
documented separation at turn.rs:262-268.)

### 9.7 Atomic paths' missing receipt — not strictly a drift but a hole

Per §4, no receipt means no comparison possible. This is the most
serious gap.

### 9.8 `FederationReceiptBody` vs. `TurnReceipt` field divergence

`FederationReceiptBody` carries `block_height`, `block_hash`, `nonce`
that `TurnReceipt` doesn't. `TurnReceipt` carries `routing_directives`,
`introduction_exports`, `derivation_records`, `emitted_events`,
`was_encrypted`, `finality`, `forest_hash`, `computrons_used`,
`action_count` that `FederationReceiptBody` doesn't. Bridging the
two requires *both*; the QC over `body_hash` only covers the body
fields. A holder of just a `FederationReceipt` cannot reconstruct
the events emitted by the turn.

### 9.9 `ArchivalAttestation.archive_terminal_receipt_hash` ↔ live chain
`last_receipt_hash` — not bound

Per §7.2. No enforcement that the archive's claimed terminal hash
equals the live chain head at the cutover.

### 9.10 `RecursiveProofVariant` does not commit to its outer receipt

Per §6.2. The recursive variant lives inside
`WitnessBundle.recursive_proof` and is identified by the bundle's
postcard hash; it has no canonical identity of its own that ties it
to a specific `TurnReceipt`.

### 9.11 `AttestedRoot` does not commit to receipt stream

`AttestedRoot.signing_message` (types/src/lib.rs:432) covers
`merkle_root` (over ledger cell states), `note_tree_root`,
`nullifier_set_root`, `height`, `timestamp`, `blocklace_block_id`,
`finality_round`, `federation_id`. **None of these are the receipt
stream root.** A federation that attested AttestedRoot R at height
H is making a statement about *ledger state*, not about *which
receipts they processed*. Two federations could agree on state at
H (same merkle_root) while having processed disjoint receipt
streams that happen to converge — at the AttestedRoot layer this
is invisible.

The implication: the AttestedRoot's commitment is *NOT* derivable
from the receipt chain alone (you can re-derive `merkle_root` by
replaying receipts from genesis through height H, but you can't
verify that the federation processed exactly the receipts the
verifier has access to). Shadow inputs: the federation's per-block
turn list. See §10 P1.

---

## §10. Closure plan — prioritized changes for Silver-Vision-completeness

### P0 — block app work / persistence-layer broken without them

**P0-1. Atomic paths emit `TurnReceipt`.** (EXECUTOR-VK-AUDIT §6.2,
this study §4.) Without this, the receipt stream has structural
holes for any agent using atomic paths; `verify_receipt_chain` can
never be a complete-history check. Closing this is the highest-
leverage architectural fix. **Effort: medium.** Add `pre_state_hash`
capture at function entry; build a receipt at commit point covering
the per-entry tuples; call `record_receipt_hash` and
`maybe_sign_receipt`. ~50-100 LOC + tests.

**P0-2. `executor_signature` covers `was_encrypted`, `finality`,
`effects_hash`.** (EXECUTOR-VK-AUDIT §6.5, this study §5.4.) Today a
signature-only verifier sees a strictly weaker statement than a
receipt-hash verifier; this is documented but exploitable in
practice (a key-rotated federation re-signing old receipts could
swap these fields and the signature would still verify). Bump
`canonical_executor_signed_message` to v3. **Effort: small.**
~20 LOC + version-compat tests.

**P0-3. Bind `EncryptedTurn.turn_commitment` into the receipt.**
(EXECUTOR-VK-AUDIT §6.6, this study §5.3.) Add
`TurnReceipt.encrypted_envelope_commitment: Option<[u8; 32]>`.
Closes the "which envelope?" gap so the ordering stream and the
receipt stream become provably-linked. **Effort: small-to-medium.**
~40 LOC + receipt-v3 bump.

### P1 — soundness / verifier-coherence

**P1-1. `ReceiptArchive` binds `archive_terminal_receipt_hash` to
the live chain head.** (This study §7.2.) The executor's apply
handler at executor.rs:10606 should additionally check that
`get_last_receipt_hash(action_target) == Some(checkpoint.
archive_terminal_receipt_hash)`. Without this the archive can be
self-asserted with no relation to the actual chain. **Effort:
small.** ~10 LOC + adversarial test.

**P1-2. `AttestedRoot` includes a `receipt_stream_root`.** (This
study §9.11.) Add a field to `AttestedRoot` committing to the
federation's per-block receipt set (Merkle root over the receipts
included in this block). Then a verifier holding an `AttestedRoot`
and a claimed receipt stream can confirm the stream is canonical.
Bump signing_message to v4. **Effort: medium.** ~60 LOC including
the block-builder update in `blocklace_sync.rs`.

**P1-3. Unify the verifiers' invariant set.** (This study §2.8.)
`verify_receipt_chain` should also check `federation_id` consistency
across the chain; `verifier::replay_chain` should also check
same-agent. Either add a `verify_receipt_chain_strict` wrapper that
runs both, or document each one's omissions in the rustdoc.
**Effort: small.** ~30 LOC + matrix tests.

**P1-4. Proof-carrying receipt populates `effects_hash` from the
proof's PI.** (EXECUTOR-VK-AUDIT §2.2, this study §9.1.) The
proof-carrying path's receipt currently has `effects_hash = H(&[])`.
Instead, extract `EFFECTS_HASH_GLOBAL` from the proof's PI and
populate the receipt. Then the receipt's effects_hash matches what
the proof attested, regardless of path. **Effort: small.** ~10 LOC.

**P1-5. `WitnessedReceipt` has its own canonical hash.** (This study
§2.5.) Currently a WR's identity collapses to its inner receipt.
Add `WitnessedReceipt::witnessed_receipt_hash() = H("dregg-wr-v1"
|| receipt_hash || H(proof_bytes) || witness_hash)`. This makes
"this WR with that proof" a content-addressable artifact. **Effort:
small.** ~15 LOC.

### P2 — coherence / future-proofing

**P2-1. `TurnReceipt` carries `vk_set_commitment`.** (EXECUTOR-VK-AUDIT
§6.1.) The receipt should commit to which (cell_id, vk_hash) pairs
the executor used. Makes the receipt VK-self-describing; required for
any constitutional migration story. **Effort: small-to-medium.**
~40 LOC + receipt v3 bump.

**P2-2. `RecursiveReceipt` as a first-class shape.** (This study §6.3.)
Lift the inner `RecursiveProofVariant` to a top-level object with
its own hash that binds the outer to the inner. Required before
Golden-Vision "drop the trace, ship only the recursive proof"
deployments are sound. **Effort: medium** (depends on AIR-SOUNDNESS-
AUDIT §2.G — the recursive AIR must first cover the full Effect VM).

**P2-3. Federation co-attestation on `ArchivalAttestation`.** (This
study §7.2.) The attestation should carry its own QC signed by the
federation, distinct from the QC on the receipt that emitted the
archive effect. **Effort: medium.** ~80 LOC including aggregator
plumbing.

**P2-4. Reconstructor-facing crate.** (Per `HOUYHNHNM-COMPARISON.md
§8.9`'s suggestion.) Land `dregg-receipts-archive` micro-crate with
`ReceiptArchive { covering_root: AttestedRoot, receipts:
Vec<WitnessedReceipt> }` as a *type* and an
`Archive::reconstruct_state()` function that exercises the §8 path
end-to-end. **Effort: medium.** Forces the gaps in §8 to surface as
test failures; the crate is small but the gaps are real.

**P2-5. Receipt-stream-as-persistence framing in docs.** (This study
§1.) Update DESIGN-receipts.md and the rustdocs on `TurnReceipt` /
`WitnessedReceipt` to name the persistence-layer role explicitly.
Not code change, but reduces the architectural-drift risk going
forward. **Effort: trivial.**

### P3 — research / aspirational

**P3-1. `RetentionPolicy` per federation member.** (HOUYHNHNM-COMPARISON
§5.1.) Per-operator config — not a protocol change but a substantial
substrate for the verifier-side "I can't serve this; here's the
attested root that covers it" wire response. **Effort: large.**

**P3-2. Cross-cell `CrossCellRecursiveReceipt`** (γ.2 Phase 2). Already
on the roadmap per PROTOCOL-CATEGORICAL-ANALYSIS §4.4. **Effort:
large**, work in flight.

**P3-3. Receipt-of-receipt chain-IVC bound into receipts themselves.**
(This study §6.2.b.) Today the IVC commitment is cclerk-local. Bound
into the receipt or the AttestedRoot, it becomes a verifiable
"running fold over the agent's history" without re-walking the chain.
**Effort: medium-to-large.**

---

## Appendix A. Field-level "what binds what" matrix

| Field | bound by `Turn::hash` | bound by `receipt_hash` | bound by `canonical_executor_signed_message` | bound by `FederationReceiptBody::body_hash` |
|---|---|---|---|---|
| agent | ✓ | ✓ | ✓ | ✓ |
| nonce | ✓ | — | — | ✓ |
| fee | ✓ | — | — | — |
| memo | ✓ | — | — | — |
| valid_until | ✓ | — | — | — |
| depends_on | ✓ | — | — | — |
| previous_receipt_hash | ✓ (on turn) | ✓ | — | ✓ |
| forest_hash | ✓ (via forest body) | ✓ | — | — |
| call_forest body | ✓ | only via turn_hash | only via turn_hash | only via turn_hash |
| execution_proof | ✓ (v3) | only via turn_hash | only via turn_hash | only via turn_hash |
| sovereign_witnesses | ✓ (v3) | only via turn_hash | only via turn_hash | only via turn_hash |
| custom_program_proofs | ✓ (v3) | only via turn_hash | only via turn_hash | only via turn_hash |
| effect_binding_proofs | ✓ (v3, gated) | only via turn_hash | only via turn_hash | only via turn_hash |
| conservation_proof | ✓ (v3) | only via turn_hash | only via turn_hash | only via turn_hash |
| pre_state_hash | (derived by executor) | ✓ | ✓ | ✓ |
| post_state_hash | (derived by executor) | ✓ | ✓ | ✓ |
| timestamp | — | ✓ | ✓ | — |
| effects_hash | — | ✓ | — | ✓ |
| computrons_used | — | ✓ | — | — |
| action_count | — | ✓ | — | — |
| federation_id | — | ✓ | ✓ | (via committee_epoch + federation_id outside body) |
| routing_directives | — | ✓ | — | — |
| introduction_exports | — | ✓ | — | — |
| derivation_records | — | ✓ | — | — |
| emitted_events | — | ✓ | — | — |
| finality | — | ✓ | — | — |
| was_encrypted | — | ✓ | — | — |
| executor_signature | — | (circular; excluded) | (the signature itself) | — |
| block_height | — | — | — | ✓ |
| block_hash | — | — | — | ✓ |
| envelope.turn_commitment | — | — | — | — |
| witness_bundle.witness_hash | — | — | — | — |
| recursive_vk_hash | — | — | — | — |

Reading: every column should be a *superset* of the chain of trust
each verifier reconstructs. Mismatches between adjacent columns
expose the bits a verifier-at-that-layer cannot independently
audit.

---

## Appendix B. Files cited

- `turn/src/turn.rs` (Turn, TurnReceipt, Finality)
- `turn/src/executor.rs` (construction sites, atomic paths,
  encrypted adapters, ReceiptArchive apply)
- `turn/src/verify.rs` (verify_receipt_chain family)
- `turn/src/witnessed_receipt.rs` (WitnessedReceipt, WitnessBundle,
  RecursiveProofVariant)
- `turn/src/action.rs` (Effect::ReceiptArchive)
- `turn/src/encrypted.rs` (EncryptedTurn, turn_commitment)
- `turn/src/journal.rs` (LedgerJournal coverage)
- `verifier/src/lib.rs` (replay_chain, replay_chain_recursive,
  check_receipt_pi_binding, ReplayEntry mirror)
- `federation/src/receipt.rs` (FederationReceipt, FederationReceiptBody)
- `federation/src/types.rs` (verify_via_receipt_chain, AttestedRoot reuse)
- `federation/src/cross_fed_bundle.rs` (CrossFedReceiptBundle)
- `cell/src/lifecycle.rs` (CellLifecycle, ArchivalAttestation,
  DeathCertificate)
- `cell/src/cell.rs` (Cell::archive, lifecycle transitions)
- `circuit/src/recursive_witness_bundle.rs` (RecursiveProofProducer,
  verify_recursive_proof_variant)
- `types/src/lib.rs` (AttestedRoot.signing_message)
- `node/src/blocklace_sync.rs` (build_federation_receipt,
  canonical_ledger_root, append_receipt sites)
- `node/src/api.rs`, `node/src/mcp.rs` (chain length, receipt-chain
  query, append sites)
- `sdk/src/cipherclerk.rs` (Cipherclerk.append_receipt, receipt_chain,
  IVC chain)
- `protocol-tests/src/invariants/receipt_chain.rs`,
  `turn/tests/proptest_invariants.rs` (chain-causality invariants)
- `DESIGN-receipts.md` (1163-line three-tier design proposal)
- `EXECUTOR-VK-AUDIT.md` §§2.2, 2.3, 4.1, 4.4, 5.4, 5.6, 5.9, 6.1,
  6.2, 6.5, 6.6, 6.7
- `AIR-SOUNDNESS-AUDIT.md` §2.G (RecursiveProofVariant coverage gap)
- `HOUYHNHNM-COMPARISON.md` §3.1, §5.1, §8.8, §8.9, §9.1
- `HOUYHNHNM-DEEP-CRITIQUE.md` §3, §4.2
- `PROTOCOL-CATEGORICAL-ANALYSIS.md` §4 (receipt operations)


# PROTOCOL-CATEGORICAL-ANALYSIS — duals, inverses, and lifecycle gaps across the protocol surface

**Date:** 2026-05-24. **Status:** study/design lane; read-only on code;
one new `.md`. **Scope:** the *rest* of dregg's protocol surface
beyond what `CROSS-CELL-CATEGORICAL-ANALYSIS.md` already covers.

**Companion docs:** `CROSS-CELL-CATEGORICAL-ANALYSIS.md` (prior lane —
Heyting / γ.2 / WitnessProducer / coequalizer-of-ring-trade /
Renunciation / Refusal / OneOf — DO NOT REPEAT),
`CROSS-CELL-COORDINATION.md`, `FEDERATION-AS-CELL.md`,
`PREDICATE-INVENTORY.md`, `DESIGN-receipts.md`,
`SLOT-CAVEATS-DESIGN.md`, `BOUNDARIES.md`,
`AUTHORIZATION-CUSTOM-DESIGN.md`,
`DESIGN-captp-integration.md`, `STORAGE-AS-CELL-PROGRAMS.md`,
`STAGE-7-GAMMA-2-PI-DESIGN.md`, `EXECUTOR-HONESTY-AUDIT.md`.

The seed observation from the user that triggered this analysis:
*"we can't… destroy cells? hmm."*

That is correct. dregg has `CreateCell`, `CreateCellFromFactory`,
`SpawnWithDelegation`, `MakeSovereign` (a creation-shaped transition
between Hosted and Sovereign modes), and a runtime
`CellMigrationManager` that *physically removes* a cell from one
federation only after acknowledgement that it has arrived at another.
*There is no first-class deliberate-destruction effect.* `Permissions::
frozen()` is the closest thing — a cell whose every action is
`AuthRequired::Impossible`, structurally undead but functionally
inert. The migration manager *deletes* cells on `Completed`, but only
because the cell has been re-created elsewhere; the deletion is a
*relocation artifact*, not an effect type. No `Effect::CellDestroy`,
no death certificate, no descendant disposition, no provable claim
that "this cell was retired at height H with reason R."

That is the seed example. The remainder of this document looks for
the other gaps of the same shape — *creation-without-destruction*,
*action-without-undo*, *grant-without-recall*, *issue-without-recall*
— across ten protocol surfaces. The categorical method names the
operator, identifies the structural dual that would complete it,
asks whether the dual is present, partial, or missing, and prioritizes
the resulting punch list as Tier 1 (foundational), Tier 2
(composability gain), or Tier 3 (nice-to-have).

The opinionated TL;DR — written first so it can be read alone:

> Across ten protocol surfaces, fourteen Tier 1 lifecycle / dual gaps
> emerge. The most foundational is **`Effect::CellDestroy` and its
> companion `DeathCertificate`**: dregg has no provable way to retire
> a cell, no first-class shape for the c-list-disposition question
> ("what happens to the descendants?"), and no audit trail that says
> "this id is permanently irreclaimable." This is the missing terminal
> object in the cell-lifecycle poset — *frozen* is "no action allowed
> right now," not "the cell is gone."
>
> Three other Tier 1 gaps cluster around the same theme: **(a) no
> `Effect::CellFork` / `CellClone`** with provable lineage commitment
> for branched delegation trees (Phase 4 sovereign cells will need
> this to split state for sharding); **(b) no `Effect::Burn` as the
> categorical dual of `Mint`** (today `NoteSpend` is the dual of
> `NoteCreate` for *notes*, but the cell-balance `Mint` from
> `EpochMinter` has no inverse — there is no provable "I destroyed N
> computrons at height H"); **(c) no `Effect::AttenuateCapability`**
> as a non-revoke restriction (today the only way to make a capability
> narrower is to revoke-and-reissue, which is racy and observable).
>
> Three Tier 1 receipt-side gaps: **(d) no `ReceiptArchive` / pruning
> primitive** with provable history-elision attestation — dregg's
> chains are append-only with no first-class shape for "this prefix
> has been archived under attestation `A`, replays start from
> snapshot `S`"; **(e) no cross-chain-receipt-of-receipt structure**
> beyond `BridgeFinalize`'s single-receipt witness; **(f) no
> `ChainTruncation` / `Tombstone` for cells whose receipt-chain is
> intentionally being abandoned.**
>
> Three Tier 1 federation gaps: **(g) no `FederationSplit` effect** —
> a federation can change its committee via `apply_epoch_transition`
> but cannot fork into two governance domains under a single attested
> transition; **(h) no `FederationMerge`** — the dual; **(i) no
> `FederationWindDown`** — committee-attested death, distinct from
> "committee is empty" which is undefined behavior today.
>
> Four Tier 2 composability gains: **(j) bearer capability
> `Renewal`** (extend an expiring bearer cap without revoke-and-
> reissue), **(k) `CapabilityRotation`** (atomic same-permission
> swiss-number rotation under key compromise broadcast), **(l)
> `EpochAdvanceAttestation`** as a first-class timeout-witnessed
> effect, **(m) `BridgeOfBridges`** — atomic chained-bridge primitive.
>
> Three Tier 3 closure points: **(n) capability discovery /
> introspection primitive** at the structural surface (today: out-
> of-band), **(o) decoy / honey capability** for adversarial-trap
> auditing, **(p) higher-order predicate witnessing** (predicate-of-
> predicates) — useful for governance-of-governance schemes.
>
> The pattern is consistent: dregg's *constructive* side is rich;
> its *destructive*, *transitive-quotient*, and *cross-time-windowed*
> sides are thin. The seed observation generalizes.

The remainder of the doc earns this in §§1–10 (one per protocol
surface), summarizes the prioritized punch list in §11, and reflects
on the meta-pattern in §12.

---

## §1. Cell lifecycle — the missing terminal object

### §1.1. Operators present

The cell creation / state-transition operators currently in tree:

| Operator | Source | Role |
|---|---|---|
| `Cell::new(pk, token_id)` | `cell/src/cell.rs:168` | Constructor (sovereign mode) |
| `Cell::new_hosted(pk, token_id)` | `cell/src/cell.rs:188` | Constructor (hosted mode) |
| `Cell::from_config(pk, token_id, config)` | `cell/src/cell.rs:290` | Configurable constructor |
| `Cell::with_balance(pk, token_id, balance)` | `cell/src/cell.rs:208` | Balance-presetting constructor |
| `Cell::spawn_child(pk, token_id)` | `cell/src/cell.rs:371` | Parent-attaches-child constructor |
| `Cell::spawn_child_with_delegation(...)` | `cell/src/cell.rs:401` | C-list-snapshotting constructor |
| `Cell::remote_stub_with_id(id)` | `cell/src/cell.rs:253` | Placeholder for foreign cells |
| `Effect::CreateCell { public_key, token_id, balance }` | `turn/src/action.rs:453` | Turn-level creation |
| `Effect::CreateCellFromFactory { factory_vk, ..., params }` | `turn/src/action.rs:760` | Factory-mediated constructor |
| `Effect::SpawnWithDelegation { ... }` | `turn/src/action.rs:540` | Snapshot-delegation child spawn |
| `Effect::MakeSovereign { cell }` | `turn/src/action.rs:751` | Hosted → Sovereign transition |
| `CellMigrationManager::begin_migration` | `turn/src/executor.rs:457` | Initiate cross-federation move |
| `CellMigrationManager::bundle_sent` / `confirm_received` / `cancel` | `turn/src/executor.rs` | Migration phase advances |
| `FactoryRegistry::deploy(descriptor)` | `cell/src/factory.rs:839` | Factory deployment |
| `FactoryDescriptor` carries `child_program_vk` + `child_vk_strategy` | `cell/src/factory.rs:269` | Templated creation |

That's the constructive side. *Together this set spans*: ex-nihilo
creation (`CreateCell`), templated creation (`CreateCellFromFactory`),
parent-child creation with delegation (`SpawnWithDelegation`),
mode-transition (`MakeSovereign`), and relocation
(`CellMigrationManager`).

### §1.2. The dual is absent

The categorical dual of "create" is "destroy." Categorically: if
*every initial-state cell has a unique morphism from `⊥` (the
uninstantiated cell)*, then *every terminal-state cell has a unique
morphism to `⊤` (the destroyed cell)*. `dregg` has the morphism *from*
`⊥`; it does not have the morphism *to* `⊤`.

What's near it:

- **`Permissions::frozen()`** (`cell/src/permissions.rs:152`) sets every
  `AuthRequired` to `Impossible`. The cell *cannot be acted upon*. But:
  - The cell *still exists* in the ledger.
  - The cell's c-list, balance, and state remain present.
  - The cell's id is *not* released — re-creation under the same
    `(pk, token_id)` is impossible because of content-addressing.
  - There is no audit trail of *who* froze it *when* and *why*.
- **`MigrationState::Completed`** (`turn/src/executor.rs:407`) results
  in cell removal from the source federation. But:
  - This is *not deliberate destruction* — it's relocation. The cell
    exists somewhere else.
  - The source federation simply *forgets* the cell; there's no
    structural attestation "this cell has departed this federation."
- **`CellMigrationManager::confirm_received`** invokes physical
  deletion. But the deletion is *implicit*: the cell is gone, nothing
  is left to point at it. No `(cell_id, departed_height,
  destination_fed_root)` tombstone.

### §1.3. Why this is a structural gap, not an ergonomic one

Three concrete questions can be asked of a *destroyed* cell that
cannot be asked of a *frozen* or *migrated* cell:

1. **"What happens to the descendants?"** A cell with children
   (`spawn_child`-spawned) has descendants that hold a `delegate:
   Some(parent_id)`. If the parent is gone, the children's
   `DelegatedRef` snapshot is *frozen at the moment of departure*.
   There is no first-class shape for "the parent died at height H;
   descendants who held a snapshot taken before H remain valid;
   descendants who try to refresh after H get `Err::ParentDestroyed`."
   Today: parent freeze leaks "I am unable to be refreshed-against"
   silently; parent migration is treated as "parent moved" not
   "parent died"; no machinery for "parent is gone."

2. **"Can the id be re-used?"** `dregg`'s content-addressed CellId is
   `BLAKE3(public_key || token_id)`. So the answer in practice is
   *no, never* — once `(pk, token_id)` is consumed, it can never be
   re-issued because the same pre-image produces the same id. This
   is *fine* as a soundness property but *terrible* as an audit
   property: there is no way to *positively assert* "this id was
   permanently retired at H," only "this id has never been observed
   to receive a turn since H." Without a death-certificate primitive,
   the absence of a turn is indistinguishable from outage / silence.

3. **"What's the cell's final receipt?"** A live cell's chain ends
   at its most recent `WitnessedReceipt`. There is no canonical
   "final receipt" that says "no more receipts after this." The chain
   *should* converge to a single attested artifact that anyone can
   sample to learn the cell has been retired. Today: nothing.

The structural absence of these three answers — *descendant
disposition*, *id-retirement attestation*, *final receipt* — *is* the
absence of `Effect::CellDestroy`.

### §1.4. Proposed primitives

**Tier 1: `Effect::CellDestroy`**

```rust
/// Permanently retire a cell.
///
/// The cell's id is recorded in a federation-level `destroyed_cells`
/// Merkle tree under the resulting `DeathCertificate` leaf. The cell
/// itself is removed from `cells` and a tombstone entry is added to
/// `tombstoned_cells` carrying the certificate hash.
///
/// Descendant disposition is specified by `dependents_policy`. The
/// permission check requires `AuthRequired::SetPermissions` (the cell
/// being able to lock itself implies the cell being able to retire
/// itself).
Effect::CellDestroy {
    /// The cell being retired.
    cell: CellId,
    /// What to do with descendants holding a `DelegatedRef` pointing
    /// at `cell`. See `DependentsPolicy` below.
    dependents_policy: DependentsPolicy,
    /// A free-form 32-byte hash of the destruction reason (commit-only;
    /// the cleartext reason lives off-chain and is referenced through
    /// the on-chain `reason_hash`).
    reason_hash: [u8; 32],
    /// Optional final-state-commitment that the cell carried at the
    /// moment of death (so verifiers can re-execute up to and including
    /// the destruction turn and confirm post-state).
    final_state_commitment: [u8; 32],
}

/// Policy for descendants of a destroyed cell.
pub enum DependentsPolicy {
    /// Existing `DelegatedRef` snapshots remain valid forever; no refresh.
    /// (Useful for "graceful retirement" where the parent's capability
    /// set is intended to outlive the parent.)
    FreezeSnapshots,
    /// Descendants are *also* destroyed (cascade death). The destruction
    /// turn must enumerate all descendants in `cascade_targets`.
    Cascade { cascade_targets: Vec<CellId> },
    /// Descendants are revoked at the federation level (their
    /// `DelegatedRef` reads return `Err(ParentDestroyed)` from this
    /// height onward).
    RevokeAll,
}
```

**Tier 1: `DeathCertificate`** (companion artifact)

```rust
/// A federation-attested artifact recording a cell's permanent retirement.
///
/// Lives in a Merkle tree at the federation level (`destroyed_cells_root`,
/// a new field on `AttestedRoot`). Verifiers can prove membership to
/// assert "this cell was retired at height H."
pub struct DeathCertificate {
    pub cell_id: CellId,
    pub destruction_turn_hash: [u8; 32],
    pub destruction_height: u64,
    pub final_state_commitment: [u8; 32],
    pub final_receipt_hash: [u8; 32],
    pub dependents_policy: DependentsPolicy,
    pub reason_hash: [u8; 32],
}
```

The federation maintains a Merkle tree of death certificates. Cross-
federation queries (e.g., from a peer that holds a sturdy ref) can
present a `DeathCertificate` membership proof to learn "the cell I
held is gone; here is its final receipt."

**Tier 1: `Effect::CellSeal` and `Effect::CellUnseal`** (separate from
destroy)

Distinct from destruction: *sealing* is a reversible
"this-cell-is-quiescent" marker. Today `Permissions::frozen()` is the
only seal-shape; it's a runtime convention, not a structural primitive.
A `CellSeal` effect would:

- Append a `seal_event` slot to the cell's state with the height + reason.
- Set permissions to `frozen()` *and* emit an attested seal event in the
  receipt.
- Allow `CellUnseal` (with the original sealer's authority) to reverse
  the seal — *which is precisely what's distinct from destroy*.

The point of separating seal/unseal from destroy: *cell sealing is
reversible*; *destruction is not*. Today both are conflated under
"frozen permissions."

**Tier 2: `Effect::CellFork` / `Effect::CellClone`**

A cell *fork* is a structural copy of cell-state into a new cell-id
with provable lineage. This is *not* the same as `spawn_child` (which
creates a fresh empty child); it's *clone-with-state*.

```rust
Effect::CellFork {
    /// The source cell being forked.
    source: CellId,
    /// The new child cell's public key (combined with parent's token_id
    /// to derive child_id, with a fork-disambiguation salt).
    child_public_key: [u8; 32],
    /// Lineage commitment: BLAKE3(source.state_commitment ||
    /// fork_height || child_pk). Stored on the child cell as
    /// `forked_from_commitment` so the lineage is verifiable.
    lineage_commitment: [u8; 32],
    /// Whether to copy the c-list, the balance, both, or neither.
    fork_kind: ForkKind,
}

pub enum ForkKind {
    /// Empty child cell — same as `spawn_child`. (Aliased here for uniformity.)
    None,
    /// Child inherits parent's c-list snapshot (= `spawn_child_with_delegation`).
    Capabilities,
    /// Child inherits parent's app_state (cleartext slots copied verbatim).
    State,
    /// Child inherits both c-list and app_state.
    Full,
}
```

Why Tier 2 (not 1): the sharding / state-splitting argument is real
(Phase 4 sovereign cells will likely want to split state across cells
for parallelism), but isn't blocking today. The structural shape *is*
worth naming.

**Tier 2: `Effect::CellAbandon`**

A `CellAbandon` is an *unrevocable* sealing — the cell explicitly
declares "I will never act again; my final state is this; if anyone
holds a delegated ref or capability, refresh requests after H will
return `Err::CellAbandoned`." Distinct from destroy in that the cell
*still occupies the ledger*; the federation can choose to garbage-
collect or not. This is the "Pacific Northwest of cells" — they go
to live their best life and don't come back.

### §1.5. Cell lifecycle summary

| Operator | Dual | Status | Tier |
|---|---|---|---|
| `CreateCell` | `CellDestroy` | **MISSING** | 1 |
| `CreateCellFromFactory` | `CellDestroy` (factory-aware) | **MISSING** | 1 |
| `SpawnWithDelegation` | `RevokeDelegation` ✓; `CellDestroy` for descendants | partial → MISSING for destroy-cascade | 1 |
| `MakeSovereign` | (no `MakeHosted`) | **MISSING** | 2 |
| `CellMigration::begin` | `CellMigration::confirm` ✓ | present | n/a |
| `CellMigration::cancel` | self-inverse | present | n/a |
| `Permissions::frozen()` | `Permissions::default()` | partial — not seal/unseal | 2 (seal) |
| (no fork) | (no fork-merge) | **MISSING** | 2 (fork) / 3 (merge) |
| (no abandon) | self-final | **MISSING** | 2 |

**Three Tier 1 items**: `CellDestroy`, `DeathCertificate`,
descendant-policy semantics. **Three Tier 2 items**: `CellSeal/Unseal`,
`CellFork`, `MakeHosted` (mode reversal). One Tier 3: `CellAbandon`.

The cell-lifecycle terminal object is the foundational gap.

---

## §2. Effect taxonomy — auditing inverse pairs across ~45 variants

### §2.1. The full taxonomy

Pulled from `turn::action::Effect` (`turn/src/action.rs:427`). The
~45 variants (using rustdoc names — some are grouped here for
exposition):

**Cell mutation:**
- `SetField { cell, index, value }` — write a slot
- `Transfer { from, to, amount }` — move computrons
- `IncrementNonce { cell }` — bump nonce
- `SetPermissions { cell, new_permissions }` — update auth requirements
- `SetVerificationKey { cell, new_vk }` — replace cell's VK

**Cell lifecycle:**
- `CreateCell { public_key, token_id, balance }`
- `CreateCellFromFactory { factory_vk, owner_pubkey, token_id, params }`
- `MakeSovereign { cell }`
- `SpawnWithDelegation { child_public_key, child_token_id, max_staleness }`
- `RefreshDelegation`
- `RevokeDelegation { child }`

**Capability ops:**
- `GrantCapability { from, to, cap }`
- `RevokeCapability { cell, slot }`
- `Introduce { introducer, recipient, target, permissions }`
- `ExerciseViaCapability { cap_slot, inner_effects }`
- `CreateSealPair { sealer_holder, unsealer_holder }`
- `Seal { pair_id, capability }`
- `Unseal { sealed_box, recipient }`

**Note operations:**
- `NoteSpend { nullifier, note_tree_root, value, asset_type, ... }`
- `NoteCreate { commitment, value, asset_type, encrypted_note, ... }`

**Bridge (cross-federation note transfer):**
- `BridgeMint { portable_proof }` (Phase 1)
- `BridgeLock { nullifier, destination, value, ... }` (Phase 2)
- `BridgeFinalize { nullifier, receipt }` (Phase 3)
- `BridgeCancel { nullifier }` (Phase 4)

**Escrow:**
- `CreateEscrow { cell, recipient, amount, condition, timeout, escrow_id }`
- `ReleaseEscrow { escrow_id, proof }`
- `RefundEscrow { escrow_id }`
- `CreateCommittedEscrow { ... }` (privacy-preserving variant)
- `ReleaseCommittedEscrow { escrow_id, claim_auth, recipient }`
- `RefundCommittedEscrow { escrow_id, claim_auth, creator }`

**Obligation:**
- `CreateObligation { beneficiary, condition, deadline_height, stake, stake_amount }`
- `FulfillObligation { obligation_id, proof }`
- `SlashObligation { obligation_id }`

**Event / observability:**
- `EmitEvent { cell, event }`

**Pipelined / eventual:**
- `PipelinedSend { target, action }`

**Queue operations:**
- `QueueAllocate { capacity, program_vk }`
- `QueueEnqueue { queue, message_hash, deposit }`
- `QueueDequeue { queue }`
- `QueueResize { queue, new_capacity }`
- `QueueAtomicTx { operations }`
- `QueuePipelineStep { pipeline_id, source, sinks }`

**CapTP runtime (Stage 7 P1.A):**
- `ExportSturdyRef { swiss_number, target }`
- `EnlivenRef { swiss_number, bearer }`
- `DropRef { ref_id }`
- `ValidateHandoff { cert_hash }`

### §2.2. Pair audit — which have inverses, which don't

Walk the list. For each effect, ask: *does there exist an inverse
effect (modulo idempotency caveats) such that
`effect ∘ inverse ≈ id`?*

| Effect | Inverse | Status |
|---|---|---|
| `Transfer { from, to, amount }` | `Transfer { from: to, to: from, amount }` | ✓ implicit |
| `Mint { cell, amount }` (via `EpochMinter`) | — | **MISSING** |
| `Burn { cell, amount }` | — | **MISSING** (this is the dual of Mint) |
| `SetField { cell, index, value }` | `SetField { cell, index, old_value }` | ✓ if old known |
| `IncrementNonce { cell }` | — (one-way) | n/a (nonce is monotonic) |
| `SetPermissions { cell, new }` | `SetPermissions { cell, old }` | ✓ if old known + signed |
| `SetVerificationKey { cell, new_vk }` | `SetVerificationKey { cell, old_vk }` | ✓ if old known + signed |
| `CreateCell` | `CellDestroy` | **MISSING** (§1) |
| `CreateCellFromFactory` | `CellDestroy` (factory-aware) | **MISSING** (§1) |
| `MakeSovereign` | `MakeHosted` | **MISSING** |
| `SpawnWithDelegation` | `RevokeDelegation` | ✓ (partial — see §2.3) |
| `RefreshDelegation` | — (idempotent monotone refresh) | n/a |
| `GrantCapability` | `RevokeCapability` | ✓ |
| `RevokeCapability` | (no un-revoke) | n/a (revocation is monotone) |
| `Introduce` | (no un-introduce) | **MISSING** (see §2.4) |
| `ExerciseViaCapability` | — (a use; idempotency depends on inner) | n/a |
| `CreateSealPair` | (no destroy-seal-pair) | **MISSING** (see §2.5) |
| `Seal` | `Unseal` | ✓ |
| `Unseal` | `Seal` | ✓ (modulo recipient change) |
| `NoteSpend` | `NoteCreate` (with the spent value) | ✓ at value-conservation layer |
| `NoteCreate` | `NoteSpend` | ✓ |
| `BridgeMint` | — (no bridge-back-out) | partial; `BridgeLock` + `BridgeCancel` is the timeout-side dual but not a deliberate un-mint |
| `BridgeLock` | `BridgeCancel` (timeout) or `BridgeFinalize` (forward) | ✓ |
| `BridgeFinalize` | (no un-finalize) | n/a (terminal) |
| `BridgeCancel` | (no un-cancel) | n/a (terminal) |
| `CreateEscrow` | `RefundEscrow` (after timeout) or `ReleaseEscrow` (with proof) | ✓ |
| `ReleaseEscrow` | (no un-release) | n/a (terminal) |
| `RefundEscrow` | (no un-refund) | n/a (terminal) |
| `CreateObligation` | `FulfillObligation` (success) or `SlashObligation` (failure) | ✓ |
| `FulfillObligation` | (no un-fulfill) | n/a (terminal) |
| `SlashObligation` | (no un-slash) | n/a (terminal) |
| `EmitEvent` | (no un-emit) | n/a (events are append-only) |
| `PipelinedSend` | (target's failure → broken promise) | partial — see `BrokenReason` |
| `QueueAllocate` | (no `QueueDestroy`) | **MISSING** |
| `QueueEnqueue` | `QueueDequeue` | ✓ |
| `QueueDequeue` | (no re-enqueue at same position) | n/a (consumes) |
| `QueueResize` | `QueueResize { new_capacity: old }` | ✓ |
| `QueueAtomicTx` | (per-op duals) | partial |
| `QueuePipelineStep` | (no inverse step) | n/a |
| `ExportSturdyRef` | `RevokeCapability` of the swiss entry / `DropRef` | partial — see §6 |
| `EnlivenRef` | `DropRef` | ✓ |
| `DropRef` | (no re-enliven from drop) | n/a |
| `ValidateHandoff` | (no un-validate; single-use leaf) | n/a (terminal) |

### §2.3. The `RevokeDelegation` pair is partial

`SpawnWithDelegation` creates a child with a c-list snapshot.
`RevokeDelegation` bumps the parent's epoch so the snapshot becomes
stale. *But*: the child cell itself is not retired, the c-list
snapshot is not erased, and a freshly-spawned child can be issued a
new delegation that overrides the staleness. There is no
*sharp* dual that says "this exact spawn is undone."

The structural completion: a `CellDestroy { cell: child }` operating
on the child *is* the sharp dual of `SpawnWithDelegation`. Until that
exists, the pair is partial.

### §2.4. `Introduce` has no inverse

`Effect::Introduce` (`turn/src/action.rs:609`) does three-party
introduction — introducer hands recipient a routable cap into target.
*There is no inverse* — no `Effect::Disintroduce` or
`Effect::WithdrawIntroduction`. The recipient now holds the cap; the
only way to break the introduction is for *target* to revoke
(`RevokeCapability`) or for *recipient* to drop (no first-class
effect — they just stop using it).

The dual that would complete this: **`Effect::WithdrawIntroduction
{ introducer, recipient, target }`** that — with the introducer's
authority — removes the introduced cap from recipient's c-list and
emits a structural attestation "this introduction was withdrawn at
height H." This matters in three places:

1. **Coercion-resistant introductions.** "I introduced Bob to my
   trading bot. Bob is now trying to drain it. I want to withdraw
   the introduction *without revoking the cap entirely* (because
   Charlie also has it via a separate introduction)."
2. **Custodial trust chains.** "I introduced Bob to my retirement
   account read-only. Bob is now untrustworthy. Withdraw."
3. **Auditable disintroduction.** A first-class artifact that says
   "the introducer disowned this introduction" — distinct from
   "the target revoked Bob's cap." The latter implies a problem with
   Bob; the former implies a problem with the introduction *as such*.

**Tier 2** — there are workarounds (revoke + reissue for everyone
who isn't Bob), but they're racy.

### §2.5. `CreateSealPair` has no destroy

`CreateSealPair { sealer_holder, unsealer_holder }` (`turn/src/action.rs:518`)
creates a long-lived sealer/unsealer pair. There is no operation to
*destroy* the pair (e.g., to retire a cryptographic primitive whose
key is compromised). Today: the holders simply stop using it, but
the pair still occupies state.

**Tier 3** — small impact; mostly a hygiene issue.

### §2.6. The `Mint` / `Burn` asymmetry

`EpochMinter::mint` (`turn/src/economics.rs`) creates computrons on
some cells per epoch (the federation's minting policy). There is no
`Effect::Burn { cell, amount }` that would let an agent provably
destroy computrons from its own balance.

Why this matters:

1. **Deflationary mechanisms.** Some app patterns need provable
   value destruction (token burns for governance, deflation against
   inflation, etc.). Today the closest is `Transfer { from, to:
   <unspendable>, ... }` — which requires a designated "burn cell"
   and isn't structurally a burn.
2. **Capability-cost prepayment.** An obligation's stake (today
   `stake_amount` in `CreateObligation`) is *locked* and either
   returned or transferred to beneficiary. There is no "stake-and-
   burn" pattern where the stake is *destroyed* rather than
   transferred — which would be the right shape for some adversarial
   compliance flows ("I burn N to commit to not violating predicate P
   in the next epoch").
3. **The structural sense.** Mint and Burn are categorically dual.
   `dregg` has note-burn (`NoteSpend` with no `NoteCreate` of equal
   value) at the value-commitment layer, but not at the cell-balance
   layer. The asymmetry is real.

**Tier 1** — adding `Effect::Burn { cell, amount }` is a small
addition with broad expressive payoff. (It's likely already needed by
*some* app surface — token-burn governance is a common pattern.)

### §2.7. Other missing inverses

**`Effect::QueueDestroy`** — Tier 1. `QueueAllocate` has no inverse.
Today the only way to retire a queue is to dequeue everything and
abandon, which leaves the queue cell occupying state forever. A
queue is a cell (in the storage-as-cell-programs model per
`STORAGE-AS-CELL-PROGRAMS.md`), so this folds into §1's
`CellDestroy` once queues are cell-shaped. Until then: standalone
primitive.

**`Effect::AttenuateCapability { cell, slot, new_facet_mask }`** —
Tier 1. Capability attenuation today is *only* available as a
revoke-and-reissue dance: revoke the cap, then issue a new one with
narrower permissions. This is racy (in the moment between revoke and
reissue, the holder has nothing) and observable (the receipt shows
both effects). A direct attenuation primitive — "narrow this cap's
facet mask, leaving the slot intact and the holder uninterrupted" —
is structurally absent.

The reason this matters: bearer capabilities and CapTP-delivered
caps are *immutable bearer artifacts* — once issued, the cap-holder
holds the cap. To attenuate, the issuer revokes and re-grants. But
this means the *holder loses* the cap entirely during the
intermediate state. With `AttenuateCapability`, the holder retains
the slot continuously, just with narrower bits set.

The shape:

```rust
Effect::AttenuateCapability {
    /// The cell whose cap is being attenuated.
    cell: CellId,
    /// Which c-list slot.
    slot: u32,
    /// New facet mask (must be a strict subset of the current mask
    /// per `is_facet_attenuation`). Enforced at executor level.
    new_facet_mask: u32,
    /// Optional new expiry (must be ≤ current expiry).
    new_expiry: Option<u64>,
}
```

Verifier check: `new_facet_mask ⊆ old_facet_mask` (subset of bits) ∧
`new_expiry ≤ old_expiry`. This is `is_narrower_or_equal` at the
slot-mask level (already in `cell/src/permissions.rs:52` for
`AuthRequired`; would extend to facet bits).

**`Effect::SetPermissions` → permission monotonicity** — partial
finding. Today `SetPermissions` is unconstrained — the cell's holder
can *widen or narrow* permissions arbitrarily. A natural structural
restriction: permission *narrowing* is always allowed under
`SetPermissions` auth; permission *widening* requires `Either`-or-
better auth (and ideally a `WideningJustification`).

This isn't strictly a missing dual, but it's a missing *monotonicity
invariant*. Categorically: `Permissions` is a poset under
`is_narrower_or_equal`; `SetPermissions` should respect the poset
structure. Today it doesn't.

**Tier 2** (composability gain).

### §2.8. Refusal, NoOp, Tombstone (from prior analysis — referencing only)

`Effect::Refusal` was discussed in the prior analysis
(`CROSS-CELL-CATEGORICAL-ANALYSIS.md §3.3`) and ruled "defer" — the
categorical pressure (initial object in Effect) is aesthetic; app
demand is thin. *No re-litigation here.* But: when `Effect::Refusal`
*does* land, it composes with `Effect::CellDestroy` naturally — a
cell can refuse to be destroyed (the `CellDestroy`-attempt produces
a `Refusal` receipt). This is a non-trivial composition that the
present analysis flags.

### §2.9. Effect taxonomy summary

| Missing inverse | Tier |
|---|---|
| `CellDestroy` (dual of `CreateCell`) | 1 |
| `Burn` (dual of mint) | 1 |
| `QueueDestroy` (dual of `QueueAllocate`) | 1 |
| `AttenuateCapability` (continuous capability narrowing) | 1 |
| `WithdrawIntroduction` (dual of `Introduce`) | 2 |
| `MakeHosted` (dual of `MakeSovereign`) | 2 |
| `CellSeal` / `CellUnseal` (reversible quiescence; distinct from destroy) | 2 |
| `DestroySealPair` (dual of `CreateSealPair`) | 3 |
| `CompensatingAction` / generic rollback | (see §2.10) |

### §2.10. The "compensating action" non-finding

A natural categorical question: does dregg have a *generic compensating
action* — an effect that says "the previous effect at slot P was wrong;
this effect compensates"? The answer is *no by design* — the executor
operates under turn-atomicity, so within a turn all effects are atomic
(commit or rollback together) and across turns the receipt chain is
append-only. The "compensating action" pattern in distributed-systems
language is *external* to dregg: it lives in the off-chain
orchestrator that observes a failed turn and *issues a new turn* to
compensate. This is correct; there is no in-protocol "rollback" because
there is nothing to roll back to.

The Tier-2 *Pending* / *Eventual* shapes (`turn::pending`,
`turn::eventual`) carry the "this turn awaits resolution" semantics
and have a `BrokenReason` (failure mode). These are the structural
shape closest to compensation — a pending turn that breaks is a
pending turn whose effect is "the obligation is now broken." Today
the `BrokenReason` is recorded; there is no first-class "compensate
broken pending" effect, but the pattern is consistent with the
external-compensation philosophy.

*No primitive proposed here.* This is a non-finding to make explicit.

---

## §3. Authorization lifecycle — issue, attenuate, recall, rotate

### §3.1. Operators present

`Authorization` is six variants (`turn/src/action.rs:191`):

- `Signature(r, s)` — Ed25519 over action hash
- `Proof { proof_bytes, bound_action, bound_resource }` — ZK proof with bound action/resource
- `Breadstuff(token)` — capability-token hash
- `Bearer(BearerCapProof)` — bearer cap with delegation chain
- `Unchecked` — terminal (anything-goes; soundness hole)
- `CapTpDelivered { handoff_cert, ... }` — CapTP-delivered receipt
- `Custom { predicate }` — app-defined witnessed predicate (per `AUTHORIZATION-CUSTOM-DESIGN.md`)

`AuthRequired` is six (`cell/src/permissions.rs:5`):
- `None`, `Signature`, `Proof`, `Either`, `Impossible`, `Custom { vk_hash }`.

The auth lifecycle operators currently in tree:

- **Issuance**: `GrantCapability` (turn-level); `Introduce` (three-party); `ExportSturdyRef` (CapTP).
- **Delegation**: `BearerCapProof` (immediate inline); `Introduce` (offline / cross-fed); CapTP `HandoffCertificate`.
- **Attenuation (caveats)**: `CapabilityCaveat`, `FacetConstraint`, `Bearer(facet_mask)`. *Compile-time only* — once a cap is granted, attenuation requires revoke-and-reissue (§2.7).
- **Composition**: `Vec<StateConstraint>` (AND); `StateConstraint::AnyOf` (OR, single-level); `Authorization::Custom` (arbitrary). Incoming Tier 1 work: `Authorization::OneOf` (per prior analysis).
- **Expiration**: `BearerCapProof::expires_at`; `HandoffCertificate::expiry_height`; cap-level via `revocation_channel`.
- **Revocation**: `RevokeCapability`; `RevocationChannel::trip`; `SwissTable::revoke`.
- **Renunciation**: incoming (per prior analysis §3.2).
- **Exhaustion (single-use)**: `ValidateHandoff` consumes the leaf; `swiss_table.entry.use_count` is one-shot in some configurations.

### §3.2. The missing rotation primitive

**Tier 2: `Effect::CapabilityRotation { cell, slot, new_swiss }`**

A capability is identified by `(cell, slot)` + a swiss number that
acts as bearer secret. When the swiss number is *compromised* — leaked,
mis-stored, observed in transit by a malicious party — the only
recovery today is `RevokeCapability` + reissue. This has the same
race/observability problem as §2.7's `AttenuateCapability`.

A *rotation* primitive would atomically swap the swiss number while
preserving slot identity and all attached metadata:

```rust
Effect::CapabilityRotation {
    cell: CellId,
    slot: u32,
    /// New swiss number (random; not derivable from the old).
    new_swiss: [u8; 32],
    /// Hash of the rotation reason (key compromise, prophylactic, etc.).
    reason_hash: [u8; 32],
}
```

Verifier check: the holder of the *old* swiss demonstrates rotation
authority; the slot identity (the c-list position) is unchanged; only
the swiss bytes update.

This composes well with:

- A *broadcast* model where the federation publishes a "swiss
  rotated" event so peers holding the old swiss know to fetch the
  new one through a CapTP handshake.
- A *key compromise broadcast* — see §3.4.

### §3.3. The missing compromise-broadcast primitive

**Tier 2: `Effect::KeyCompromise { compromised_pk, replacement_pk,
attestation }`**

A cell's public key is its identity (content-addressed). If the cell's
*signing key* is compromised, the cell is gone — there's no way to
say "this pk was compromised; do not trust signatures from it after
height H." The cell can transition to `Permissions::frozen()` to halt
all action, but any *prior* signatures remain accepted (as they
should — they were valid at signing time).

What's missing: a *forward-looking* primitive that says "anything
signed under `compromised_pk` after height H should be rejected by
peers; here is the replacement_pk."

This is hard because the replacement cell has a *different id* (it's
content-addressed). So the structural shape is:

```rust
Effect::KeyCompromise {
    /// The compromised cell.
    compromised_cell: CellId,
    /// Height at which the compromise was discovered.
    discovered_at: u64,
    /// Optional replacement cell (same agent, new pk → new id).
    replacement_cell: Option<CellId>,
    /// Cryptographic attestation of the compromise (e.g., a turn
    /// signed by the compromised key declaring its own compromise,
    /// recorded as a one-way invariant).
    attestation: KeyCompromiseAttestation,
}
```

The federation maintains a `compromised_keys` Merkle tree (parallel
to the revocation tree). Peers consulting the tree learn:
- Any signature dated *after* `discovered_at` from `compromised_pk`
  should be rejected.
- An optional pointer to the replacement cell for continuity.

**Why Tier 2**: the alternative — abandon the cell, spawn a new one,
re-grant all caps — is doable today but requires off-chain
coordination. A first-class primitive saves the coordination dance.

### §3.4. The missing "exhausted capability" attestation

**Tier 3: `Effect::CapabilityExhausted { cell, slot }`**

A single-use capability (e.g., a handoff certificate whose
`approved_handoffs_root` leaf is consumed) is *implicitly* exhausted
after first use. The exhaustion is *not* recorded as a first-class
receipt; it's a side-effect of the membership-leaf consumption.

A `CapabilityExhausted` effect would emit a structural artifact "this
cap was exercised its final time at height H" — distinct from
`RevokeCapability` (which is *authority-initiated*) and from
`MakeSovereign` (which is *cell-transition*). The audit value: a
verifier inspecting the c-list can distinguish "cap N still has uses
left" from "cap N is exhausted, ignore it."

**Why Tier 3**: small enough that the workaround (caller polls the
single-use counter) suffices.

### §3.5. The Heyting / negation / implication asymmetry (per prior analysis)

`StateConstraint::Not` and `Implies` are in tree per the prior
analysis (`CROSS-CELL-CATEGORICAL-ANALYSIS.md §3.1`, codified in
`cell/src/program.rs:505`). The composability gain for *authorization*
specifically:

- "Authorize iff the holder is in the approved set AND NOT on the
  blocklist." Today: encodable as `WitnessedPredicate::Custom` with a
  bespoke AIR. With `Not` at the auth-predicate layer: structural.

This is already incoming via the Heyting work. *No new primitive
proposed here.*

### §3.6. Capability tree pruning — the missing structural fold

A capability *delegation chain* (`BearerCapProof::DelegationProof`)
is structurally a tree: root issuer → first delegate → second
delegate → ... → bearer. Today there is no first-class shape for
*pruning* the tree — i.e., for a mid-tree delegate to attest "the
subtree rooted at me is no longer valid" without going through every
descendant.

The shape:

```rust
Effect::PruneDelegationSubtree {
    /// The delegate at the root of the subtree being pruned.
    root_delegate: PublicKey,
    /// Federation-level Merkle commitment to "subtree pruned at H."
    /// Verifiers walking a chain whose root_delegate is in the
    /// pruned set reject the chain.
    subtree_root_commitment: [u8; 32],
}
```

**Tier 2** — useful for delegation-tree governance ("the legal team
delegated to all-of-engineering; engineering is now reorganized;
prune the legal team's delegation"). Workaround: every leaf's
`revocation_channel` must be individually tripped.

### §3.7. Authorization lifecycle summary

| Operator | Status / dual | Tier |
|---|---|---|
| `GrantCapability` ↔ `RevokeCapability` | ✓ | n/a |
| `Introduce` ↔ (no `WithdrawIntroduction`) | **MISSING** | 2 |
| Expiration ↔ (no `Renewal`) | **MISSING** | 2 (see §3.8) |
| Single-use ↔ (no `CapabilityExhausted` receipt) | **MISSING** | 3 |
| Rotation (no primitive) | **MISSING** | 2 |
| Key compromise broadcast | **MISSING** | 2 |
| Delegation subtree pruning | **MISSING** | 2 |
| `Not` / `Implies` in caveats | landing (prior lane) | — |
| Renunciation | landing (prior lane) | — |
| `OneOf` | landing (prior lane) | — |
| `Authorization::Unchecked` (soundness hole) | partial — see audit | — |

### §3.8. Renewal as the dual of expiration

A bearer cap has `expires_at: u64`. The dual of "expiry" is
"renewal" — extending the expiry without revoke-and-reissue. Today:
issuer revokes the old cap, issues a new one. Race-prone (§2.7
again).

A `RenewBearerCapability` would extend `expires_at` while preserving
the original delegation chain proof:

```rust
Effect::RenewBearerCapability {
    /// The original cap being renewed.
    original_target: CellId,
    original_slot: u32,
    /// New expiry (must be > current; may be ≤ original-issuer's
    /// maximum-allowed expiry, enforced at issuer level).
    new_expires_at: u64,
    /// Renewal signature by the original delegator chain head.
    renewal_signature: [u8; 64],
}
```

**Tier 2** (composability gain).

---

## §4. Receipt / chain operations — the missing archival, fork, and recursive shapes

### §4.1. Operators present

The receipt-side machinery:

- `WitnessedReceipt` (`turn/src/witnessed_receipt.rs:243`) — proof-carrying receipt with public inputs, witness bundle, recursive proof.
- `WitnessedReceipt::from_components` / `from_components_with_compression` / `from_components_strict_recursive` — construction.
- `WitnessedReceipt::verify_bilateral_chain` — γ.2 cross-cell consistency check.
- `WitnessedReceipt::chain_to_json` / `chain_from_json` — serialization.
- `verify_receipt_chain` (`turn/src/verify.rs`) — chain validation.
- `TurnReceipt::previous_receipt_hash` — chain linkage.
- `AggregateMembership` — cross-cell receipt aggregation hook (v1: always `None`).
- `WitnessBundle::inline_with_recursive` — recursive proof compression (Golden Vision form).
- `CrossFedReceiptBundle` (`federation/src/cross_fed_bundle.rs`) — cross-federation receipt bundling.
- `Checkpoint` (`federation/src/checkpoint.rs`) — federation-level periodic snapshots.

### §4.2. Append-only chain has no archival primitive

The receipt chain is *append-only forever*. There is no first-class
shape for:

- "Truncate the chain prior to height H; the truncation is attested;
  replays start at H."
- "Archive heights [A, B] to off-chain storage; the archival is
  attested; live nodes need only retain [B+1, ∞)."
- "Provide a *witness of archival* — a verifier can confirm that the
  attestation is well-formed and the off-chain blob hash matches."

Why this matters:

1. **Storage cost.** Long-lived cells (e.g., a federation-shared
   pool cell that has been running for years) accumulate unbounded
   receipt chain. Today everyone must keep all of it.
2. **Replay cost.** Scope-2 replay walks the whole chain. With
   archival attestation + checkpoint, replays could start from the
   checkpoint.
3. **Privacy.** Old receipts may need to be purged for regulatory
   reasons. Today: no way to do this provably.

**Tier 1: `Effect::ReceiptArchive`**

```rust
Effect::ReceiptArchive {
    /// The cell whose chain is being archived.
    cell: CellId,
    /// The chain prefix being archived: heights [archive_start, archive_end].
    archive_start_height: u64,
    archive_end_height: u64,
    /// BLAKE3 of the off-chain archival blob (the serialized chain prefix).
    archive_blob_hash: [u8; 32],
    /// The state-commitment at archive_end_height (post-state of last
    /// receipt in the archived prefix).
    archive_terminal_commitment: [u8; 32],
    /// The receipt hash at archive_end_height (so the live chain's
    /// `previous_receipt_hash` link is preserved).
    archive_terminal_receipt_hash: [u8; 32],
    /// Federation-level attestation that this archive is canonical.
    /// On commit, the federation adds (cell, archive_blob_hash) to a
    /// `archived_prefixes` Merkle tree.
    federation_attestation: ArchivalAttestation,
}
```

The first receipt *after* the archive carries
`previous_receipt_hash == archive_terminal_receipt_hash` — the chain
remains linked, just with the prefix replaced by a single attested
pointer. Replayers seeking heights ≤ `archive_end_height` consult
off-chain storage; replayers verifying recent activity walk only the
live tail.

This is a real ergonomic and storage win.

### §4.3. No first-class receipt fork

A *receipt chain fork* would arise structurally when:

- Two competing branches exist (a Byzantine federation produces two
  receipts at the same height claiming different states).
- A deliberate forensic branch (a federation operator branches the
  chain to test a counterfactual).

Today: the receipt chain is *posetal* (chain) and any divergence is
unsoundness. There is no structural shape for "this is a *deliberate
branch* with an attested divergence point and resolution policy."

**Tier 3** — too niche to prioritize. The honest categorical
observation: receipt chains are *trees with a single canonical path
selected by federation consensus*, and the absence of a "branch
declaration" effect reflects dregg's commitment to consensus-decided
linearity. *No primitive proposed*; this is a clarifying observation.

### §4.4. Receipt-of-receipt — the recursive structure

The categorical name for "a receipt that verifies another receipt"
is *recursive proof composition*. Today dregg has this — partially:

- `WitnessBundle.recursive_proof: Option<RecursiveProofVariant>` —
  a proof verifying a base proof.
- `chain-IVC` (per `STAGE-7-PLUS-DESIGN.md`) — folding multiple
  receipts into a single chain proof.

But there is no first-class *cross-cell* recursive receipt — "this
receipt attests that *cell A's receipt at height H* is consistent
with *cell B's receipt at height K*, both verified inside the
recursive circuit."

This is the categorical limit of γ.2 — the recursive completion of
bilateral binding. Per `STAGE-7-GAMMA-2-PI-DESIGN.md` Phase 2, this
is on the roadmap (Joint Bilateral Aggregation AIR). When it lands,
the structure will be:

```rust
pub struct CrossCellRecursiveReceipt {
    /// The cross-cell pair being attested.
    pair: (CellId, CellId),
    /// Each cell's WitnessedReceipt at the relevant height.
    receipts: (WitnessedReceipt, WitnessedReceipt),
    /// The recursive proof: a SNARK that verifies both base proofs
    /// and asserts γ.2 consistency in-circuit.
    aggregate_proof: Vec<u8>,
    /// Public inputs: the canonical effect_id, both state commitments.
    aggregate_pis: Vec<u32>,
}
```

**Not yet a Tier-1 primitive** because the Phase 2 work is in flight.
Flag in the punch list as "expect to land via γ.2 Phase 2."

### §4.5. Pinning — the missing immutability declaration

A *pinned* receipt is one that the federation *commits to never
archive*. This is useful for:

- Audit-critical receipts that regulators require be retained
  perpetually.
- Receipts that anchor cross-fed bridges (the destination federation
  may need to query them years later).

Today: implicit — federations retain receipts at their discretion.

**Tier 3: `Effect::ReceiptPin { receipt_hash, retention_policy }`**

```rust
Effect::ReceiptPin {
    receipt_hash: [u8; 32],
    /// How long to retain. `Forever` means "include in checkpoint
    /// merkle root permanently."
    retention_policy: RetentionPolicy,
}

pub enum RetentionPolicy {
    Forever,
    UntilHeight(u64),
    UntilFederationDecision,
}
```

### §4.6. Receipt operations summary

| Operator | Dual / lifecycle pair | Status | Tier |
|---|---|---|---|
| Chain extension (`previous_receipt_hash`) | Chain truncation | **MISSING** | 1 |
| Archival | — (no antecedent) | **MISSING** | 1 |
| Recursive proof (intra-cell) | ✓ | landing | n/a |
| Recursive proof (cross-cell) | — | landing (γ.2 Phase 2) | n/a |
| Fork attestation | (no canonical branch) | n/a (consensus-linear) | — |
| Pinning | unpinning (just expiry) | **MISSING** | 3 |
| Checkpoint | — (terminal) | ✓ | n/a |

### §4.7. The "chain tombstone" companion to cell destruction

Tying back to §1: when `Effect::CellDestroy` lands, the cell's
receipt chain *terminates*. The terminal receipt is the
"chain-tombstone" — a receipt that says "this is the last
receipt; verifiers seeking heights > H should reject." Today
there's no such marker because there's no `CellDestroy`. This is
captured by §1's `DeathCertificate.final_receipt_hash`.

---

## §5. Federation lifecycle — committee transitions, split, merge, wind-down

### §5.1. Operators present

`Federation` (`federation/src/federation.rs:91`) has:

- `Federation::from_committee(...)` — constructor
- `Federation::solo(local_seat)` — single-member federation
- `Federation::verifier_only(...)` — read-only stub
- `apply_epoch_transition(new_members, new_epoch, new_threshold)` — committee rotation in place (federation id changes, because id is `derive_federation_id_with_epoch(members, epoch)`)
- `Federation::build_attested_root(...)` — produce an `AttestedRoot` bound to this federation
- `Federation::verify_receipt` / `verify_attested_root` — cross-fed verification
- `FederationCommittee` (BLS threshold committee)
- `ThresholdQC::aggregate` / `verify` — BLS signature aggregation
- `Checkpoint` — periodic snapshot
- `derive_federation_id_with_epoch(members, epoch)` — content-addressed identity

There is no "create a federation from scratch" effect at the *turn*
level; federations are bootstrapped out-of-band. There is no
"destroy a federation" effect at any level. There is no "fork a
federation" effect. There is no "merge two federations" effect.

### §5.2. Member join / leave

Per `apply_epoch_transition`: members may be added or removed by
rotating the entire committee. *There is no first-class "this member
joined" or "this member left" effect.* The committee change is *all-
or-nothing* under an epoch boundary.

This is fine *for governance* (an epoch transition is the natural
moment for committee changes) but *not for forensics*: a verifier
looking at the committee diff between epoch N and epoch N+1 cannot
distinguish "Alice was kicked for malfeasance" from "Alice
voluntarily left" from "Alice's key was rotated to her new
representative" — they all show up as "the committee changed."

**Tier 3: a `MemberDeparture` event** that, alongside the epoch
transition, records *why* the membership change occurred. Companion
to the federation's checkpoint, not a separate effect.

### §5.3. Federation split — the missing colimit

**Tier 1: `Effect::FederationSplit`**

Real-world need: governance domain divergence. A federation serving
both retail-bank and crypto-exchange use cases decides to split into
two governance domains (different compliance requirements, different
upgrade cadence, etc.). Today: the only way is *socially* to
bootstrap a new federation, migrate the relevant cells, and abandon
the old federation. There's no provable structural shape.

The proposed primitive:

```rust
Effect::FederationSplit {
    /// The source federation being split.
    source_fed_id: FederationId,
    /// Resulting federation A's committee.
    fed_a_members: Vec<PublicKey>,
    fed_a_threshold: u32,
    /// Resulting federation B's committee.
    fed_b_members: Vec<PublicKey>,
    fed_b_threshold: u32,
    /// Cell-disposition mapping: which cells go to A, which to B,
    /// which are shared (jointly attested by both).
    cell_partition: CellPartition,
    /// Quorum signature from the source federation authorizing the split.
    source_authorization: ThresholdQC,
}

pub struct CellPartition {
    pub to_fed_a: Vec<CellId>,
    pub to_fed_b: Vec<CellId>,
    pub shared: Vec<CellId>, // jointly attested
}
```

On commit:
- The source federation produces a final attested root with
  `split_height = H`.
- Fed A and Fed B are bootstrapped at height H+1 with the partitioned
  cell sets. Their first `AttestedRoot` chains back to the source's
  `split_height`.
- Cells in `shared` carry a *bilateral* membership marker; both
  federations attest their state, and any cross-fed bridge between A
  and B treats `shared` cells with a special joint-witnessing path.

This is the categorical *pushout* of the federation-as-cell structure
at the federation layer — `FederationSplit` is the colimit that the
prior analysis (§5.2 of `CROSS-CELL-CATEGORICAL-ANALYSIS.md`) didn't
specifically name (it focused on cross-cell pushouts, not cross-fed).

### §5.4. Federation merge — the missing colimit's dual

**Tier 1: `Effect::FederationMerge`**

Dual: two federations decide to merge. Today: not expressible.
Proposed:

```rust
Effect::FederationMerge {
    /// The two federations being merged.
    fed_a_id: FederationId,
    fed_b_id: FederationId,
    /// Resulting merged federation's committee.
    merged_members: Vec<PublicKey>,
    merged_threshold: u32,
    /// Quorum signatures from both source federations.
    fed_a_authorization: ThresholdQC,
    fed_b_authorization: ThresholdQC,
    /// Resolution policy for conflicting state (e.g., a cell id
    /// somehow on both federations under different state; or a
    /// nullifier that's been used on A and B).
    conflict_resolution: ConflictResolution,
}

pub enum ConflictResolution {
    /// Reject the merge if any conflicts exist.
    Strict,
    /// Take fed_a's view for conflicts.
    PreferA,
    /// Take fed_b's view for conflicts.
    PreferB,
    /// Custom resolution per cell (a Merkle witness per conflicting cell).
    Custom { resolution_root: [u8; 32] },
}
```

Tier 1 because: federation mergers are a real pattern (industry
consolidation), and without a structural primitive there is no audit
trail of *who attested the merge under which conflict-resolution
policy*.

### §5.5. Federation wind-down

**Tier 1: `Effect::FederationWindDown`**

A federation that decides to *retire* — distinct from being split or
merged. The cells migrate to other federations (or are destroyed);
the committee dissolves; the federation id is recorded as retired in
some directory.

```rust
Effect::FederationWindDown {
    fed_id: FederationId,
    /// Final attested root before wind-down.
    final_root: AttestedRoot,
    /// Quorum signature authorizing the wind-down.
    authorization: ThresholdQC,
    /// Disposition: where do the cells go?
    cell_disposition: WindDownDisposition,
}

pub enum WindDownDisposition {
    /// Every cell is migrated to the named destination federation.
    MigrateAllTo(FederationId),
    /// Cells are partitioned across multiple destinations.
    MigratePartitioned(HashMap<CellId, FederationId>),
    /// All cells are destroyed (via §1's `CellDestroy`).
    DestroyAll,
}
```

The dual: in `Federation`'s "committee with 0 members" we have an
"empty committee" — but the federation's logic is undefined in this
state. `FederationWindDown` makes the wind-down an *explicit
attested act*, not an undefined-behavior corner.

### §5.6. The takeover / coup-detection question

**Tier 3 observation:**

A federation can have its committee *seized* if a critical mass of
member keys are compromised. Today there's no first-class shape for
"the committee has been subverted; trust nothing after height H."
The closest is `KeyCompromise` (§3.3) per-member, but coordinating a
group-level compromise broadcast is not currently structural.

**Possible primitive: `Effect::FederationCompromiseBroadcast`** —
out of scope here, but flagged. The honest engineering call is that
*if* a federation is compromised, the recovery path is *out-of-
protocol* (peer federations refuse to trust the compromised
federation, social escalation, etc.). A first-class shape inside the
compromised federation is fundamentally suspect — the compromised
committee will produce whatever message it wants.

### §5.7. Cross-federation handshake (per `FED-AS-CELL`)

The prior `CROSS-CELL-CATEGORICAL-ANALYSIS.md §4.2` identified the
"asymmetric axis" — federations don't have a `peer_exchange` analog.
This is the cell↔federation adjunction's failure of naturality.

A proposed cross-fed direct handshake is not redone here. **Reference
only** to `FEDERATION-AS-CELL.md §9` recommendation.

### §5.8. Federation lifecycle summary

| Operator | Dual / lifecycle pair | Status | Tier |
|---|---|---|---|
| `from_committee` | (no `wind_down`) | **MISSING** | 1 |
| `apply_epoch_transition` | self-inverse | ✓ | — |
| Member-join | Member-leave (no first-class) | partial | 3 |
| (no `FederationSplit`) | (no `FederationMerge`) | **MISSING** | 1 (both) |
| Cross-fed handshake | (asymmetric) | partial — flagged in prior lane | — |
| Checkpoint | — (terminal) | ✓ | — |
| Compromise broadcast | — | non-applicable | — |

---

## §6. Capability lifecycle — issuance, handoff, sturdy serialization, OCapN completeness

### §6.1. Operators present

CapTP machinery (`captp/src/lib.rs`):

- `SwissTable::export` — register a swiss number / capability mapping at a federation.
- `SwissTable::enliven` — bearer presents swiss number, gets routing entry.
- `SwissTable::revoke` — retire a swiss entry.
- `ExportGcManager::record_export` / `process_drop` — distributed GC.
- `ImportGcManager` — peer-side import tracking.
- `HandoffCertificate::create` / `verify_signature` — three-party handoff cert.
- `HandoffPresentation::create` / `verify_recipient_signature` — recipient-signed presentation.
- `validate_handoff` — federation-side cert validation.
- `MessageRelay::queue_for_offline` / `deliver` (store_forward) — offline cap delivery.
- `DreggUri` (sturdy URI) — `dregg://fed_id/cell_id/swiss`.
- Pipelined sends: `PipelinePromiseState`, `PipelinedMessage`, etc.

At the turn level:

- `Effect::GrantCapability { from, to, cap }`
- `Effect::RevokeCapability { cell, slot }`
- `Effect::Introduce { introducer, recipient, target, permissions }` — three-party
- `Effect::ExportSturdyRef { swiss_number, target }` — CapTP export to chain
- `Effect::EnlivenRef { swiss_number, bearer }` — CapTP enliven on chain
- `Effect::DropRef { ref_id }` — CapTP GC decrement
- `Effect::ValidateHandoff { cert_hash }` — handoff acceptance

### §6.2. Sturdy-ref serialization / cross-federation export

A sturdy ref is a `dregg://fed_id/cell_id/swiss` URI. Anyone holding
the URI can present it to the named federation and (if the swiss is
valid) receive a live routing entry.

The lifecycle is rich but not complete. Specifically:

- *Export* (turn-level): `ExportSturdyRef` ✓
- *Enliven* (turn-level): `EnlivenRef` ✓
- *Drop* (turn-level): `DropRef` ✓
- *Revoke* (federation-level): `SwissTable::revoke` ✓
- *Re-export under new swiss*: **MISSING** (rotation §3.2 covers this)
- *Sturdy of sturdy* (delegate a sturdy without enlivening): **MISSING** (see §6.4)

### §6.3. Three-party handoff completeness

The handoff protocol:

1. *Introducer* registers a swiss entry at *target* federation.
2. *Introducer* creates a signed `HandoffCertificate` naming *recipient*.
3. Cert travels out-of-band (URI, QR, BLE, etc.).
4. *Recipient* presents cert + sign-back.
5. *Target* validates and creates routing entry.

This is *the* OCapN three-party introduction shape. **Status: ✓
present.**

But two structural points:

**(a) No first-class "introduction proof"** at the receipt level —
when target accepts the handoff, the receipt records `ValidateHandoff
{ cert_hash }` but does *not* record the recipient's identity or the
introducer's identity directly. They're inside the cert; verifiers
reconstruct from the cert hash. This works, but produces friction for
audit tooling that wants to enumerate "all introductions made by X
in epoch N" — the index must be built off-chain.

**Tier 3: a `IntroductionIndex` companion record** at the federation
level (Merkle-indexed by introducer pk) for audit ergonomics. Not a
primitive; a derived data structure.

**(b) No third-order delegation** — capability-of-capability. Today:
Alice can introduce Bob to a target via `Introduce`. Bob can then
introduce Charlie to the *same* target (granting Charlie a cap that
Bob holds). This is delegation-of-delegation, and it works.

What's *missing* is *delegation-of-delegation-authority itself* —
"Alice grants Bob the authority to grant introductions to this target
to any third party, but Alice retains the *meta-authority* to revoke
Bob's introduction-granting power." This is *third-order delegation*
in the cap-system sense.

**Tier 2: `Effect::GrantIntroductionAuthority`**

```rust
Effect::GrantIntroductionAuthority {
    granter: CellId,
    grantee: CellId,
    target: CellId,
    /// Scope of grantee's introduction authority.
    scope: IntroductionScope,
}

pub enum IntroductionScope {
    /// Grantee can introduce any third party.
    Anyone,
    /// Grantee can only introduce parties from this allowed set.
    Whitelist(Vec<CellId>),
    /// Grantee can introduce up to N parties.
    BoundedCount(u32),
}
```

### §6.4. Sturdy-of-sturdy — delegation without enlivening

Today: to delegate a sturdy ref to a third party, the original holder
shares the URI. The third party then has *the same* sturdy ref. There
is no way to issue a *narrower* sturdy that, when enlivened, grants a
*subset* of the original's permissions — without going through a
handoff certificate.

The categorical question: a sturdy ref is a *bearer secret*. Issuing
a *narrowed bearer secret* (a fresh swiss that maps to a subset of
the original's facet bits) is the structural shape of "attenuating a
sturdy."

**Tier 2: `Effect::DeriveAttenuatedSturdy`**

```rust
Effect::DeriveAttenuatedSturdy {
    /// The base sturdy being attenuated.
    base_swiss: [u8; 32],
    /// The new (narrower) sturdy.
    derived_swiss: [u8; 32],
    /// Subset of facet bits granted by the derived sturdy.
    facet_mask: u32,
    /// Optional expiry on the derived sturdy.
    expiry: Option<u64>,
}
```

This is the structural completion of "sturdy refs as bearer secrets":
they should compose under attenuation the same way capabilities do.

### §6.5. Decoy / honey capabilities

**Tier 3 observation:**

A *decoy capability* is a cap that *looks valid* to a casual
observer but *triggers detection* when exercised — a honey-pot for
adversaries. Examples:

- A cap whose first use logs the caller's identity to an alert
  channel before refusing.
- A cap that mimics a high-value target but actually grants nothing.

`dregg` has no first-class "decoy" shape. The closest is `Permissions::
frozen()` + an `EmitEvent` on attempted access. A structural primitive
would be:

```rust
Effect::GrantDecoyCapability {
    from: CellId,
    to: CellId,
    decoy_target: CellId,
    /// Channel to alert when the decoy is exercised.
    alert_channel: ChannelId,
}
```

**Tier 3** — adversarial-honeypot tooling is niche; defer.

### §6.6. Capability discovery / introspection

**Tier 3 observation:**

There is no first-class "list the caps in my c-list" effect. Today:
the holder reads their own `CapabilitySet` out-of-band. For
introspection by a *peer* (e.g., "Alice wants to delegate a cap but
doesn't remember which slot it's in"), there is no structural
primitive — Alice queries her own ledger view.

This is fine for sovereign / hosted local use; it's awkward for
federation-wide views. A first-class `EnumerateCapabilities` shape
would standardize the surface, but it's a small win.

### §6.7. The OCapN lineage check

OCapN (the cap-system specification) defines:

- *Sturdy refs* as offline-shareable identity-carrying tokens. ✓
- *Live refs* enlivened from sturdy. ✓
- *Three-party handoff* with introducer-signed certs. ✓
- *Distributed GC* (refcount across nodes). ✓
- *Promise pipelining* (pipelined sends to unresolved targets). ✓
- *Vat-shutdown attestation* — when a vat (a CapTP endpoint) shuts
  down, peers learn that all its imports are dead. **PARTIAL**
  in dregg (a cell going to `Permissions::frozen()` is the closest
  analog, but it doesn't broadcast to importers).
- *Promise rejection forwarding* — when a pipelined target turns out
  to be broken, the rejection propagates to downstream pipelined
  sends. **PARTIAL** — `BrokenReason` exists, propagation is partial.

The OCapN lineage check: dregg implements ~80% of OCapN. The gaps
are:

1. **Vat-shutdown** (would be `Effect::CellSeal` / `CellDestroy` per
   §1). Tier 1.
2. **Promise rejection propagation** (would be a `PipelinePromiseState::
   Broken` chain walker). Partial today; **Tier 2** to harden.
3. **Capability attenuation in handoff** (would be `Effect::
   DeriveAttenuatedSturdy` per §6.4). Tier 2.

### §6.8. Capability lifecycle summary

| Operator | Dual / lifecycle pair | Status | Tier |
|---|---|---|---|
| Issue (`GrantCapability`) | Revoke ✓ | ✓ | — |
| Introduce (3-party) | Withdraw introduction | **MISSING** | 2 (per §2.4) |
| Bearer issue | Renewal | **MISSING** | 2 |
| Bearer issue | Rotation | **MISSING** | 2 (per §3.2) |
| Sturdy export | Sturdy attenuation (derive narrower) | **MISSING** | 2 |
| Sturdy export | Sturdy revoke ✓ | ✓ | — |
| 3rd-order delegation (grant introduction authority) | — | **MISSING** | 2 |
| Vat-shutdown attestation | — | **MISSING** | 1 (folds into §1) |
| Distributed GC | ✓ | ✓ | — |
| Decoy / honey caps | — | **MISSING** | 3 |
| Capability enumeration | — | **MISSING** | 3 |

---

## §7. Predicate / DFA / WitnessedPredicate combinators

### §7.1. Operators present

`WitnessedPredicateKind` (`cell/src/predicate.rs:206`) enumerates:

- `Dfa` — DFA over typed input
- `Temporal` — temporal predicate via `temporal_predicate_dsl`
- `MerkleMembership` — set inclusion
- `NonMembership` — set exclusion (sorted-set neighbor proof)
- `BlindedMembership` — set inclusion against a blinded commitment
- `BridgePredicate` — bridge-fact attestation
- `PedersenEquality` — committed-value equality
- `Custom { vk_hash }` — open-ended

`StateConstraint` (`cell/src/program.rs:570`) — 22 variants today
(per prior lane's count + the new `Not` and `AnyOf` already-landed).

`SimpleStateConstraint` (`cell/src/program.rs:438`) — restricted
subset (12 variants) usable inside `Not` and `AnyOf`.

Predicate combinators present:

- Conjunction: `Vec<StateConstraint>` (implicit AND).
- Disjunction: `StateConstraint::AnyOf` (OR, single-level).
- Negation: `SimpleStateConstraint::Not` (boxed; restricted inner).
- Implication: derived via `SimpleStateConstraint::implies` → `AnyOf[Not(P), Q]`.
- Transition guards: `TransitionCase` over (method, effects_mask).

### §7.2. Quantification — the missing structural shape

The Heyting work brings the *propositional* fragment (∧, ∨, ¬, ⇒).
The first-order fragment (∃, ∀) is not surfaced.

**∃ (existential) over witness sets** is *implicitly* present:
`MerkleMembership` is "∃ leaf in this tree such that…"
`NonMembership` is "∀ leaf in this sorted tree, leaf ≠ x" (equivalent
to ¬∃ x). The witnessing-existence shape is conventional.

**∀ (universal) over a bounded set** is *not* directly expressible.
A predicate like "every leaf in the audit tree is well-formed" requires
either:
- A custom AIR that loops over the tree (expensive and structurally
  bespoke), or
- A range-proof / aggregation argument (recursive).

**Tier 2: `WitnessedPredicateKind::ForAll`**

```rust
WitnessedPredicateKind::ForAll {
    /// Commitment to the set being universally quantified over.
    set_commitment: [u8; 32],
    /// Inner predicate that must hold for every element.
    inner_kind: Box<WitnessedPredicateKind>,
}
```

This is a *higher-order* predicate shape: it composes a predicate over
elements into a predicate over sets. The Yoneda observation: every
"∀x. P(x)" predicate is determined by `(set_commitment, inner_kind)`
under verifier composition — the universal property of products
(in `Predicate^I` for an indexing set `I`).

**Tier 2** because: the demand is real (audit-style invariants) but
the workaround (custom AIR per use) carries the load.

### §7.3. Higher-order predicates — predicate-of-predicates

**Tier 3 observation:**

A *predicate over predicates* is structurally a meta-witness: "the
holder of cap `c` has been authorized to invoke predicate kind `K` —
prove that `K`'s vk_hash is in this approved registry." `dregg` has
this *implicitly* (cap-holders are identified by signature; the
predicate registry is a federation-level config). But it's not
*reifiable as a first-class predicate*.

The structural shape:

```rust
WitnessedPredicateKind::MetaPredicate {
    /// Commitment to the predicate-kind registry.
    registry_commitment: [u8; 32],
    /// The inner predicate kind being meta-witnessed.
    inner_kind_hash: [u8; 32],
}
```

Use case: governance-of-governance. "The bank board may authorize
which compliance predicates are valid for this account. The compliance
officer's predicate-set is itself attested by the board's vote." This
is two-level governance — meta-predicates make it structural.

**Tier 3** — niche but elegant. Defer until app demand surfaces.

### §7.4. Bounded recursion

A bounded-recursion predicate is "this property holds for at most N
recursive applications of a predicate template." Today: `Temporal`
predicates carry a recursion bound via the `num_steps` parameter.

Categorically: `Temporal` is the *bounded-iteration* shape; there is
no *unbounded-iteration* shape (which would require non-termination
arguments).

**Status: present at the temporal-predicate layer.** *No new
primitive proposed.*

### §7.5. Disjunction depth — the documented gap

`StateConstraint::AnyOf` is single-level only (per
`SLOT-CAVEATS-EVALUATION.md` Finding 4). This is a *depth limit*,
not a missing dual.

**Tier 2: recursive AnyOf**. Once `AnyOf` is recursive, conjunction
and disjunction become truly dual under the lattice law. Already
flagged in the prior lane; *reference only.*

### §7.6. Predicate combinator summary

| Combinator | Status | Tier (if missing) |
|---|---|---|
| ∧ (Vec) | ✓ | — |
| ∨ (AnyOf single-level) | partial | 2 (recursive AnyOf) |
| ¬ (Not, restricted inner) | landing (prior lane) | — |
| ⇒ (Implies, derived) | landing (prior lane) | — |
| ∃ (existential) | implicit (Merkle) | — |
| ∀ (universal) | **MISSING** as first-class kind | 2 |
| Higher-order predicate-of-predicates | **MISSING** | 3 |
| Bounded recursion | ✓ (Temporal) | — |
| Unbounded recursion | n/a (out of scope) | — |

---

## §8. Storage / queue / programmable substrate

### §8.1. Operators present

After the storage-as-cell-programs migration (per
`STORAGE-AS-CELL-PROGRAMS.md`), storage primitives are mostly
cell-shaped. The pre-migration types still exist:

- `MerkleQueue` (`storage/src/queue.rs:16`) — durable FIFO.
- `CapInbox` (`storage/src/inbox.rs:12`) — quota-aware capability message inbox.
- `ProgrammableQueue` (`storage/src/programmable.rs:47`) — programmable validator.
- Content storage with quota / erasure / dedup / relay primitives.
- `PolyQueue` (KZG-based; gated on `kzg` feature).

At the turn level (queue-as-cell):

- `Effect::QueueAllocate { capacity, program_vk }`
- `Effect::QueueEnqueue { queue, message_hash, deposit }`
- `Effect::QueueDequeue { queue }`
- `Effect::QueueResize { queue, new_capacity }`
- `Effect::QueueAtomicTx { operations }`
- `Effect::QueuePipelineStep { pipeline_id, source, sinks }`

Programmable queue program API (`turn/src/queue_programs.rs`):

- `QueueProgram` — VK + descriptor for queue admission control.
- `QueueConstraint` — predicate over enqueue attempts.
- `QueueProgramRegistry` — runtime registry of programs.
- `validate_enqueue` — admission check.

### §8.2. The dead-letter handling gap

A queue can fill (back-pressure) or its messages can be undeliverable
(no consumer). Today:

- `QueueAllocate` sets `capacity`; over-capacity attempts fail at
  `QueueEnqueue`.
- `CapInbox::receive` checks deposit ≥ `min_deposit`; rejects
  otherwise.
- `CapInbox::enforce_backpressure` enables time-based eviction (∼GC).

But there is no first-class "dead letter" effect — when a message is
rejected or evicted, the deposit is *refunded to the sender* (via
`ComputronRefund`) but the *fact of the rejection* is not a
first-class artifact. The sender learns through `ComputronRefund`
delivery; downstream observers can't query "what messages were
rejected in epoch N?"

**Tier 2: `Effect::QueueDeadLetter { queue, message_hash, reason }`**

```rust
Effect::QueueDeadLetter {
    queue: CellId,
    /// The rejected message's content hash.
    message_hash: [u8; 32],
    /// Reason for rejection.
    reason: DeadLetterReason,
    /// The original sender's identity (for refund routing).
    original_sender: CellId,
}

pub enum DeadLetterReason {
    CapacityFull,
    BelowMinDeposit { provided: u64, required: u64 },
    PredicateRejected,
    Evicted { evicted_at_epoch: u64 },
    Expired { ttl: u64 },
}
```

The structural value: queues become *observable* in their failure
modes, not just their happy paths.

### §8.3. The backpressure attestation gap

When a queue applies backpressure (rejects an enqueue, evicts an
entry), there's no structural artifact attesting "backpressure was
applied at height H under policy P." Auditing why messages were lost
requires reconstructing from `ComputronRefund` deliveries.

**Tier 3: `Effect::BackpressureAttestation`** — first-class artifact.
Composes with `QueueDeadLetter` (which is *per-message*); this is
*per-epoch* / *per-policy*.

### §8.4. Ordering guarantees and the missing reordering primitive

Queues today are FIFO. There is no first-class "reorder under policy"
primitive — e.g., priority-aware dequeue, deadline-aware dequeue,
sender-aware dequeue. `MessagePriority` exists in
`store_forward.rs:99` for the relay layer; it doesn't surface at
turn-level queue ops.

**Tier 3: `Effect::QueueDequeueByPriority`** — small ergonomic win;
defer.

### §8.5. Queue lifecycle — the destroy gap

§2.7 flagged `QueueDestroy` as missing. Folds into §1's `CellDestroy`
once queues are fully cell-shaped per `STORAGE-AS-CELL-PROGRAMS.md`.

### §8.6. PubSub topic lifecycle

`storage::pubsub` provides a pub/sub primitive. Topic lifecycle:

- Topic creation: implicit (first publish creates the topic).
- Topic subscription: per-cell.
- Topic destruction: **MISSING** — no first-class "retire this topic."

**Tier 3: `Effect::PubSubTopicRetire`** — folds into cell-destroy if
topics are cell-shaped.

### §8.7. Atomic / multi-asset / sharded — present

- `Effect::QueueAtomicTx` — atomic multi-op queue transactions ✓.
- `storage::multi_asset` — multi-asset accounting ✓.
- `storage::sharding` — sharded content storage ✓.

No structural gaps in these surfaces beyond the queue-lifecycle ones
above.

### §8.8. Storage substrate summary

| Operator | Dual / lifecycle pair | Status | Tier |
|---|---|---|---|
| `QueueAllocate` | `QueueDestroy` | **MISSING** | 1 (via §1) |
| `QueueEnqueue` | `QueueDequeue` ✓ | ✓ | — |
| Capacity backpressure | `DeadLetter` artifact | **MISSING** | 2 |
| Backpressure attestation | — | **MISSING** | 3 |
| FIFO ordering | Priority reorder | **MISSING** | 3 |
| Topic creation | Topic retirement | **MISSING** | 3 |
| Programmable validator | ✓ | ✓ | — |

---

## §9. Bridge / cross-chain — lifecycle and chain pinning

### §9.1. Operators present

Bridge primitives (note-level cross-federation transfer):

- `Effect::BridgeMint { portable_proof }` — Phase 1: present portable proof, mint locally.
- `Effect::BridgeLock { nullifier, destination, value, asset_type, timeout_height, spending_proof }` — Phase 2: lock at source.
- `Effect::BridgeFinalize { nullifier, receipt }` — Phase 3: finalize with destination's receipt.
- `Effect::BridgeCancel { nullifier }` — Phase 4: timeout-cancellation.

Plus the bridge crate (`bridge/`):

- `BridgePresentationProof` / `verify_presentation` — portable proof verification.
- `PortableActionBinding` — bind action to portable proof.
- `BridgeCommittedThresholdProof` — committed threshold for bridge facts.
- `BridgePredicateProof` — witnessed predicate for bridge attestation.
- Midnight observer pattern (`bridge/src/midnight_observer.rs`) — observation bridge.

### §9.1.1. The 4-phase lifecycle is clean

The bridge 4-phase protocol is *categorically clean*:

- Lock ↔ Cancel (timeout dual) ✓
- Lock ↔ Finalize (success terminal) ✓
- Cancel ↔ Finalize (mutually exclusive terminals) ✓
- Mint (one-shot import) — paired implicitly with the source's Lock ✓

This is one of the cleanest pieces of the protocol. **No new
primitives proposed for the core 4-phase lifecycle.**

### §9.2. Dispute / slashing — partial

If a bridge counterparty (e.g., the destination federation refusing
to honor a `BridgeFinalize`) misbehaves, the dispute mechanism is:

- The source can `BridgeCancel` after timeout.
- The source can slash via `SlashObligation` if a bonded obligation
  was attached.

There's no *first-class* "bridge dispute" shape that says "the
destination produced a receipt that conflicts with the source's
view." Today: a discrepancy surfaces in the source's verification
of `BridgeFinalize.receipt` and rejects.

**Tier 2: `Effect::BridgeDispute`**

```rust
Effect::BridgeDispute {
    /// The bridge transaction being disputed.
    nullifier: [u8; 32],
    /// The disputing federation.
    disputer: FederationId,
    /// Evidence of the discrepancy.
    evidence: DisputeEvidence,
}

pub enum DisputeEvidence {
    /// Destination's receipt has wrong value.
    ValueMismatch { expected: u64, claimed: u64 },
    /// Destination's receipt names wrong asset.
    AssetMismatch { expected: u32, claimed: u32 },
    /// Two conflicting destination receipts.
    DoubleFinalize { receipt_a: BridgeReceipt, receipt_b: BridgeReceipt },
}
```

Tier 2 because: the workaround (manual dispute via off-chain
escalation) suffices for the current scale.

### §9.3. Oracle attestation — partial

The bridge currently treats the *destination's signed receipt* as the
authoritative attestation. There is no general "oracle attestation"
primitive for external facts (e.g., a price feed, a regulatory
attestation, a TLS notary proof).

**Tier 3: `Effect::OracleAttest { oracle_id, fact_hash, attestation }`**

```rust
Effect::OracleAttest {
    /// The oracle's identity (federation, signature key, etc.).
    oracle_id: [u8; 32],
    /// Hash of the attested fact.
    fact_hash: [u8; 32],
    /// The attestation itself (signature or proof).
    attestation: OracleAttestation,
}
```

This is the structural completion: today, oracle attestations are
embedded in app-level effects via `Custom`; a first-class shape would
unify the oracle pattern.

**Tier 3** — defer until oracle-bridge apps need the structural
unification.

### §9.4. Bridge-of-bridges — atomic chain

A *bridge-of-bridges* is "transfer X from fed A to fed C, where the
only route is A → B → C." Today: this requires two sequential
bridge cycles (A → B, then B → C), with the asset visible on B in
between.

A *bridge-of-bridges* primitive would atomically chain the bridges:
the asset never *settles* on B; it's structurally a single atomic
relay.

**Tier 2: `Effect::BridgeChain`**

```rust
Effect::BridgeChain {
    /// Source federation.
    source: FederationId,
    /// Intermediate hops (in order).
    intermediaries: Vec<FederationId>,
    /// Destination federation.
    destination: FederationId,
    /// The transfer details.
    transfer: BridgeTransferDetails,
    /// Per-hop proofs that the relay was accepted (off-chain
    /// pre-staged proofs).
    hop_proofs: Vec<BridgeRelayProof>,
}
```

**Tier 2** — the demand is real (multi-hop liquidity routing) but
the atomic-multi-fed coordination is hard. Phase 2-level Golden
Vision work.

### §9.5. Bridge lifecycle summary

| Operator | Status | Tier (if missing) |
|---|---|---|
| Lock ↔ Cancel | ✓ | — |
| Lock ↔ Finalize | ✓ | — |
| Mint (import side) | ✓ | — |
| Dispute primitive | **MISSING** | 2 |
| Oracle attestation (generic) | **MISSING** | 3 |
| Bridge-of-bridges atomic chain | **MISSING** | 2 |
| Cross-effect chain pinning | ✓ (via prior lane work) | — |

---

## §10. Time / scheduling / liveness

### §10.1. Operators present

Time primitives:

- Federation height — `AttestedRoot::height` is the canonical clock.
- `Checkpoint` at periodic heights.
- `apply_epoch_transition` advances epoch.
- `EpochMinter::mint` operates per epoch.
- `current_epoch(block_height)` (intent/src/lib.rs:521).

Time-bound effects:

- `BridgeLock::timeout_height` ✓
- `CreateEscrow::timeout_height` ✓
- `CreateObligation::deadline_height` ✓
- `BearerCapProof::expires_at` ✓
- `Conditional::deadline` / `MAX_CONDITIONAL_DEADLINE` ✓
- `HandoffCertificate::expiry_height` ✓
- `DelegatedRef::max_staleness` ✓
- `StateConstraint::TemporalGate { not_before, not_after }` ✓
- `StateConstraint::FieldGteHeight` / `FieldLteHeight` ✓
- `StateConstraint::RateLimit { ... }` (per-epoch rate limit) ✓

Slot caveats already cover most time-bound structural shapes
(per `SLOT-CAVEATS-DESIGN.md`).

### §10.2. The missing timeout-witnessed effect

A `BridgeCancel` after timeout *implicitly* witnesses that "the
timeout has elapsed without finalization." But the witness is
*absent from the receipt's structural shape* — the receipt records
"the cancel happened at height H" but does not include "the cancel
was authorized because timeout_height ≤ H and no finalization
occurred."

The structural completion: every timeout-triggered effect should
carry a *witness of elapse*. Today: implicit (executor checks
height ≥ timeout); explicit shape:

**Tier 2: `TimeoutWitness` companion data**

```rust
pub struct TimeoutWitness {
    /// The timeout height that was reached.
    timeout_height: u64,
    /// The current federation height when the witness was recorded.
    observed_at_height: u64,
    /// Proof that no contradicting effect occurred in [timeout_height, observed_at_height].
    /// For BridgeLock: proof of non-membership of `nullifier` in the
    /// finalized-bridges set at height observed_at_height.
    non_occurrence_proof: NonOccurrenceProof,
}
```

This is the *temporal* analog of `WitnessedPredicate`: it witnesses
*"no event of type X happened in window W"*. Composes naturally with
Heyting `Not` over events.

### §10.3. Scheduled-future effects

A *scheduled future effect* is "this effect should execute at height
H, with no further turn submitted." Today: no first-class shape.
The closest is `ConditionalTurn` (per `turn/src/conditional.rs`) —
but that's *conditional on a proof being presented* by a third party,
not *time-triggered autonomously*.

**Tier 2: `Effect::ScheduleFutureEffect`**

```rust
Effect::ScheduleFutureEffect {
    /// When to execute.
    target_height: u64,
    /// The effect to execute.
    effect: Box<Effect>,
    /// Authorization at scheduling time (the future execution
    /// inherits the scheduler's authorization commitment).
    scheduler_commitment: [u8; 32],
    /// Optional cancellation policy (some scheduled effects should
    /// be cancellable; others not).
    cancellation_policy: CancellationPolicy,
}

pub enum CancellationPolicy {
    /// Cannot be cancelled.
    Irrevocable,
    /// Scheduler can cancel before target_height.
    SchedulerCancellable,
    /// A custom predicate can authorize cancellation.
    PredicateCancellable { vk_hash: [u8; 32] },
}
```

This composes with:

- Bridge timeouts (scheduled `BridgeCancel`).
- Escrow refunds (scheduled `RefundEscrow`).
- Obligation slashing (scheduled `SlashObligation`).

Today each of those is *triggered by a turn from an interested
party*. With `ScheduleFutureEffect`, the federation can execute
autonomously at the target height. **Tier 2** — this is a significant
shift in liveness model; defer until carefully designed.

### §10.4. Time-locked unlock

A *time-locked unlock* is "this cap / state / value becomes
exercisable at height H." `StateConstraint::TemporalGate` covers the
*caveat-side* form. There's no *effect-side* form — i.e., an effect
that *creates* a time-locked structural artifact.

**Tier 3: `Effect::CreateTimeLock`**

Companion to `TemporalGate`. Folds into the broader "scheduled
effects" story (§10.3); flag only.

### §10.5. Monotonic-clock attestation across federations

Each federation has its own height clock. Cross-federation
*temporal* claims ("event A on fed X happened before event B on fed
Y") require *clock synchronization*.

Today: implicit via blocklace finality rounds (`finality_round` on
`AttestedRoot`). There's no first-class "cross-fed monotonic clock"
witness.

**Tier 3: `Effect::CrossFedTimestampAttest`** — niche; defer.

### §10.6. The liveness witness — "this cell is still alive"

A *liveness witness* is "this cell has produced a turn within the
last K epochs." Useful for governance ("if any committee member
hasn't been live for 100 epochs, remove them") and for cap-revocation
("a cap on a dead cell should be considered exhausted").

Today: implicit (the executor can scan for cells with stale
`updated_at`); not first-class.

**Tier 3: `Effect::LivenessAttest { cell, last_activity_height }`** —
self-attested liveness. Tier 3 because the read-only inference is
cheap.

### §10.7. Time / liveness summary

| Operator | Status | Tier (if missing) |
|---|---|---|
| Height-bounded caveats | ✓ | — |
| Timeout-driven cancellation (Bridge, Escrow) | ✓ | — |
| Per-epoch rate limit | ✓ | — |
| Witness of timeout-elapse | **MISSING** | 2 |
| Scheduled future effect | **MISSING** | 2 |
| Time-locked unlock effect | **MISSING** | 3 |
| Cross-fed monotonic clock attest | **MISSING** | 3 |
| Liveness witness | **MISSING** | 3 |
| Slot caveats (general) | ✓ | — |

---

## §11. Prioritized punch list

Compiled from §§1–10, grouped by tier and surface. *Excludes*
findings from the prior `CROSS-CELL-CATEGORICAL-ANALYSIS.md` lane
(Heyting/Not/Implies, WitnessProducer, Unilateral γ.2,
RingClosureAttestation, Renunciation, Refusal, OneOf).

### §11.1. Tier 1 — foundational gaps

**Cell lifecycle (§1):**

| # | Primitive | Purpose | Surface |
|---|---|---|---|
| T1-1 | `Effect::CellDestroy` | Provable deliberate cell retirement | `turn::action::Effect` |
| T1-2 | `DeathCertificate` | Federation-level attested artifact of cell retirement | `federation` (new module / extension to `AttestedRoot`) |
| T1-3 | `DependentsPolicy` (Cascade / FreezeSnapshots / RevokeAll) | Descendant disposition on parent destroy | `cell` / `turn` |

**Effect taxonomy (§2):**

| # | Primitive | Purpose | Surface |
|---|---|---|---|
| T1-4 | `Effect::Burn { cell, amount }` | Provable computron destruction (dual of Mint) | `turn::action::Effect` |
| T1-5 | `Effect::QueueDestroy` | Provable queue retirement (subsumes into T1-1 when queues are fully cell-shaped) | `turn::action::Effect` or storage |
| T1-6 | `Effect::AttenuateCapability` | Continuous (non-racy) capability narrowing | `turn::action::Effect` |

**Receipt operations (§4):**

| # | Primitive | Purpose | Surface |
|---|---|---|---|
| T1-7 | `Effect::ReceiptArchive` | Attested chain-prefix archival with pointer | `turn::action::Effect` |
| T1-8 | Federation `archived_prefixes` Merkle tree | Backing data for T1-7 | `federation::AttestedRoot` |

**Federation lifecycle (§5):**

| # | Primitive | Purpose | Surface |
|---|---|---|---|
| T1-9 | `Effect::FederationSplit` | Provable two-way governance fork | `turn::action::Effect` + `federation` bootstrap |
| T1-10 | `Effect::FederationMerge` | Provable two-way governance unification | `turn::action::Effect` + `federation` bootstrap |
| T1-11 | `Effect::FederationWindDown` | Provable federation retirement | `turn::action::Effect` + `federation` bootstrap |

**Total: 11 Tier 1 primitives**, clustered around the *missing
destructive / merge / split operations*. The unifying theme: *dregg
is rich in creation, thin in deliberate termination*.

### §11.2. Tier 2 — composability gains

**Cell lifecycle (§1):**

| # | Primitive | Purpose |
|---|---|---|
| T2-1 | `Effect::CellSeal` / `Effect::CellUnseal` | Reversible quiescence (vs. irreversible destroy) |
| T2-2 | `Effect::CellFork` | Lineage-attested state-clone |
| T2-3 | `Effect::MakeHosted` | Dual of `MakeSovereign` |
| T2-4 | `Effect::CellAbandon` | Self-final unrevocable seal |

**Effect taxonomy (§2):**

| # | Primitive | Purpose |
|---|---|---|
| T2-5 | `Effect::WithdrawIntroduction` | Dual of `Introduce` |
| T2-6 | Permissions monotonicity (widen requires `Either+`) | Soundness invariant on `SetPermissions` |

**Authorization lifecycle (§3):**

| # | Primitive | Purpose |
|---|---|---|
| T2-7 | `Effect::CapabilityRotation` | Atomic swiss-number rotation without revoke-reissue |
| T2-8 | `Effect::KeyCompromise` (+ federation `compromised_keys` tree) | Forward-looking key compromise broadcast |
| T2-9 | `Effect::PruneDelegationSubtree` | Subtree revocation without per-leaf trips |
| T2-10 | `Effect::RenewBearerCapability` | Expiry extension without revoke-reissue |

**Capability lifecycle (§6):**

| # | Primitive | Purpose |
|---|---|---|
| T2-11 | `Effect::DeriveAttenuatedSturdy` | Narrower bearer secret derived from base |
| T2-12 | `Effect::GrantIntroductionAuthority` | Third-order delegation (delegating the right-to-introduce) |
| T2-13 | OCapN promise-rejection propagation completion | Harden `BrokenReason` walker |

**Predicate combinators (§7):**

| # | Primitive | Purpose |
|---|---|---|
| T2-14 | `WitnessedPredicateKind::ForAll` | Universal quantification over committed sets |
| T2-15 | Recursive `AnyOf` | Disjunction depth completion (per prior lane) |

**Storage substrate (§8):**

| # | Primitive | Purpose |
|---|---|---|
| T2-16 | `Effect::QueueDeadLetter` | First-class dead-letter artifact |

**Bridge (§9):**

| # | Primitive | Purpose |
|---|---|---|
| T2-17 | `Effect::BridgeDispute` | Structural discrepancy claim |
| T2-18 | `Effect::BridgeChain` | Atomic multi-hop bridge |

**Time / scheduling (§10):**

| # | Primitive | Purpose |
|---|---|---|
| T2-19 | `TimeoutWitness` companion data | Structural witness of timeout elapse |
| T2-20 | `Effect::ScheduleFutureEffect` | Autonomous height-triggered execution |

**Total: 20 Tier 2 primitives**, focused on *composability and audit
ergonomics*. None are blocking; all are wins.

### §11.3. Tier 3 — nice-to-have, defer

**Cell lifecycle (§1):** none (Tier 1 / 2 covered).

**Effect taxonomy (§2):**

| # | Primitive | Purpose |
|---|---|---|
| T3-1 | `Effect::DestroySealPair` | Hygiene for retiring sealer/unsealer |

**Authorization lifecycle (§3):**

| # | Primitive | Purpose |
|---|---|---|
| T3-2 | `Effect::CapabilityExhausted` (receipt artifact) | First-class single-use exhaustion mark |

**Federation lifecycle (§5):**

| # | Primitive | Purpose |
|---|---|---|
| T3-3 | `MemberDeparture` event (companion to `apply_epoch_transition`) | Audit ergonomics for committee diff |

**Capability lifecycle (§6):**

| # | Primitive | Purpose |
|---|---|---|
| T3-4 | `Effect::GrantDecoyCapability` | Honey-pot capabilities |
| T3-5 | Capability enumeration primitive | Introspection ergonomics |
| T3-6 | `IntroductionIndex` derived data | Audit-side index of introductions |

**Predicate combinators (§7):**

| # | Primitive | Purpose |
|---|---|---|
| T3-7 | `WitnessedPredicateKind::MetaPredicate` | Predicate-of-predicates / governance-of-governance |

**Receipt operations (§4):**

| # | Primitive | Purpose |
|---|---|---|
| T3-8 | `Effect::ReceiptPin` | Explicit retention policy |

**Storage substrate (§8):**

| # | Primitive | Purpose |
|---|---|---|
| T3-9 | `Effect::BackpressureAttestation` | Per-epoch backpressure artifact |
| T3-10 | `Effect::QueueDequeueByPriority` | Priority-aware dequeue |
| T3-11 | `Effect::PubSubTopicRetire` | Topic lifecycle terminator |

**Bridge (§9):**

| # | Primitive | Purpose |
|---|---|---|
| T3-12 | `Effect::OracleAttest` (generic) | Structural unification of oracle attestations |

**Time / scheduling (§10):**

| # | Primitive | Purpose |
|---|---|---|
| T3-13 | `Effect::CreateTimeLock` | First-class time-locked unlock |
| T3-14 | `Effect::CrossFedTimestampAttest` | Cross-fed clock synchronization witness |
| T3-15 | `Effect::LivenessAttest` | Self-attested liveness witness |

**Total: 15 Tier 3 primitives.** All defer-without-loss.

### §11.4. Punch list grand total

**11 Tier 1** + **20 Tier 2** + **15 Tier 3** = **46 missing
primitives.** This is large, but the *interconnections* reduce the
landed surface significantly:

- T1-1 / T1-2 / T1-3 (`CellDestroy` + `DeathCertificate` + dependents
  policy) are *one cohesive landing* — 1 effect, 1 federation
  artifact, 1 enum.
- T1-5 (`QueueDestroy`) and T2-1 (`CellSeal`) fold into the
  `CellDestroy` family once queues / inboxes / topics are fully
  cell-shaped.
- T1-9 / T1-10 / T1-11 (federation split / merge / wind-down) are
  *one cohesive landing* — the federation-lifecycle effect family.
- T2-7 / T2-8 / T2-9 / T2-10 (capability rotation, compromise
  broadcast, prune subtree, renew) are *one cohesive auth-lifecycle
  family* with shared federation-side bookkeeping.

Estimated landing units:

- **Unit A** (Cell lifecycle): T1-1, T1-2, T1-3, T2-1, T2-2, T2-3,
  T2-4 — *the cell-destruction family*.
- **Unit B** (Federation lifecycle): T1-9, T1-10, T1-11 — *the
  federation-lifecycle family*.
- **Unit C** (Auth rotation + compromise + renewal + prune): T2-7,
  T2-8, T2-9, T2-10 — *the capability-rotation family*.
- **Unit D** (Receipt archival): T1-7, T1-8 — *the chain-archival
  family*.
- **Unit E** (Effect symmetries): T1-4 (Burn), T1-6
  (`AttenuateCapability`), T2-5 (`WithdrawIntroduction`), T2-6
  (permission monotonicity) — *the inverse-effect-pair family*.
- **Unit F** (OCapN completion): T2-11, T2-12, T2-13 — *the OCapN
  closure family*.
- Smaller units (Tier 2/3 odds and ends): predicate ∀, scheduled
  effects, dead-letter, bridge dispute, etc.

Six landing units capture the bulk; the remainder is sweep work.

---

## §12. Meta-reflection — why is dregg asymmetric this way?

Two honest observations close out the analysis.

### §12.1. The bias toward creation

`dregg`'s design rhythm — visible from the inventory above — is
*"how do we build this thing safely?"* much more than *"how do we
retire this thing safely?"* This is *normal* for a Phase-1 system:
the creative half of the algebra accrues mass first because
creating-a-cell, granting-a-cap, writing-a-state, executing-a-turn
*are* the protocol's reason for existing. The destructive half
accrues mass when the system has been live long enough to need it.

What this analysis suggests is that dregg *is* now mature enough to
need the destructive half. The seed observation ("we can't destroy
cells?") generalizes — and the punch list shows it generalizes
*widely*. Cells, queues, federations, introductions, sturdies,
delegation subtrees — every creation point in the substrate is
missing its retirement point.

The *categorical* observation: dregg is rich in initial morphisms
("morphisms from `⊥` into the substrate") and thin in terminal
morphisms ("morphisms from the substrate to `⊤`"). The prior lane's
analysis already named this for `Predicate` (no `False`) and
`Effect` (no `Refusal`). The present analysis names it for *cells*,
*queues*, *federations*, *sturdies*, *delegation trees*, and
*receipts*.

The unifying primitive shape would be a *generic terminator* —
something like `Effect::Retire<T>` parameterized by object kind.
That's probably too cute; the specialized primitives in the Tier 1
list are clearer. But the *pattern* — "every creation morphism
deserves its retirement morphism" — is the structural truth here.

### §12.2. The bias toward bilateral, away from k-ary

The prior lane's analysis flagged this: γ.2 bilateral is canonical;
trilateral (Introduce) is special-cased; k-ary (multilateral atomic)
is *intentionally* not provided. The present analysis surfaces the
same pattern at *federation* level:

- One-fed operations are canonical.
- Two-fed operations (Bridge, FederationMerge if added) are pairwise.
- Three-fed-or-more operations have no first-class shape (only
  pairwise compositions).

This is a *design commitment*, not a gap. `dregg` deliberately resists
k-ary primitives — the verifier-loop complexity and the consensus-
coordination complexity argue against them. The pairwise composition
is *expected* to be the workhorse.

The Tier 2 `Effect::BridgeChain` is the *first place this commitment
softens* — atomic multi-hop bridges *do* need k-ary structure. The
analysis doesn't recommend changing the commitment, but it does flag
that as dregg scales, the *one place* the k-ary pressure becomes
real is in liquidity-routing bridges. Watch this surface.

### §12.3. The "improve don't degrade" thesis

Per `[Improve Don't Degrade]` in the user's project memory: when an
audit finds a gap, fix it; never downgrade a ProofTier or add
"experimental" flags to reflect known gaps. This analysis is
*entirely* improvement-side: every Tier 1 item is "add this
primitive," not "carve out a soundness hole." The Tier 1 list is
~11 primitives over ~4 cohesive landings (Cell-destroy family,
Federation-lifecycle family, Receipt-archival family,
Effect-symmetries family), each of which is a real *upgrade* to the
substrate without lowering any of dregg's current invariants.

The categorical hygiene is *additive*. Every primitive proposed here
*completes* a missing dual without weakening any existing one.

### §12.4. What this analysis is honest about not having

Three honest limits of this analysis:

1. **AIR-side cost is not estimated.** Every Tier 1 effect needs an
   Effect VM AIR variant. Adding 11 new Effect variants means 11 new
   AIR variants. The Silver Vision punch list (per `NEW-WORLD.md
   §233`) already has 9 placeholder AIR variants; adding 11 more
   would expand that backlog. The categorical analysis says
   *"these primitives should exist"*; it does not estimate
   *"how much engineering"*.

2. **Per-app demand is not surveyed.** Every Tier 2 / 3 primitive
   should ideally be tied to a specific app's structural need. This
   analysis projects from the algebra; the app-demand verification
   is a separate lane.

3. **Cross-tier interactions are not exhaustively explored.** E.g.,
   how does `Effect::CellDestroy` interact with `Effect::
   PipelinedSend` whose target is the destroyed cell? (Answer:
   `BrokenReason::TargetDestroyed`, but not explicitly designed.)
   How does `Effect::FederationSplit` interact with in-flight
   bridges? (Answer: presumably the bridges complete under one of
   the two resulting federations, but the partition policy needs
   spec work.) The interactions are sketched, not specified.

These three limits mean the punch list is *categorical hygiene*, not
*ready-to-implement specification*. The next lane after this would
be per-primitive design docs.

---

## §13. References

- `CROSS-CELL-CATEGORICAL-ANALYSIS.md` — prior lane (Heyting / γ.2 /
  WitnessProducer / RingClosureAttestation / Renunciation / Refusal /
  OneOf).
- `STORAGE-AS-CELL-PROGRAMS.md` — storage-as-cells migration.
- `FEDERATION-AS-CELL.md` — federation/cell adjunction.
- `AUTHORIZATION-CUSTOM-DESIGN.md` — `Authorization::Custom`.
- `DESIGN-receipts.md` — receipt-chain shape.
- `STAGE-7-GAMMA-2-PI-DESIGN.md` — γ.2 PI design.
- `SLOT-CAVEATS-DESIGN.md` / `SLOT-CAVEATS-EVALUATION.md` — slot
  caveat layer.
- `BOUNDARIES.md` — four-fold boundary discipline.
- `EXECUTOR-HONESTY-AUDIT.md` — soundness ledger.
- `NEW-WORLD.md` — overall vision (Silver / Golden).
- `turn/src/action.rs` (Effect enum, lines 427–877).
- `cell/src/cell.rs` (Cell type, lifecycle constructors).
- `cell/src/factory.rs` (FactoryDescriptor, ChildVkStrategy).
- `cell/src/program.rs` (CellProgram, StateConstraint, SimpleStateConstraint).
- `cell/src/predicate.rs` (WitnessedPredicate, registry).
- `cell/src/permissions.rs` (Permissions, AuthRequired).
- `cell/src/revocation_channel.rs` (RevocationChannel).
- `captp/src/lib.rs` and submodules (sturdy, handoff, gc).
- `federation/src/federation.rs` (Federation type, epoch transition).
- `intent/src/lib.rs` / `solver.rs` / `trustless.rs` (intent
  matching, ring solver).
- `storage/src/queue.rs` / `inbox.rs` / `programmable.rs`.
- `bridge/src/present.rs` (BridgePresentationProof family).
- `turn/src/witnessed_receipt.rs` (WitnessedReceipt).
- `turn/src/executor.rs` (CellMigrationManager, MigrationState).

---

End of analysis.

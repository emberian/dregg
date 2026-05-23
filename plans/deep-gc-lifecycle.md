# Deep GC as Migration: A Unified State Lifecycle

The core insight: garbage collection and migration are the same operation viewed
from different economic perspectives. When state becomes too expensive to keep,
the cheapest GC is "migrate it somewhere cheaper." The cheapest migration target
is the owner's own device (sovereignty).

This document unifies five existing mechanisms into a single coherent lifecycle:
1. CapTP distributed GC (`captp/src/gc.rs`)
2. Storage metering / state rent (`turn/src/executor.rs`, computron costs)
3. Constitutional timeout (`blocklace/src/constitution.rs`, `LeaveReason::Timeout`)
4. IVC history compression (`circuit/src/ivc.rs`)
5. Cell migration (`plans/vat-migration-design.md`)

---

## The Five Phases of Cell Life

```
 BIRTH ──── ACTIVE ──── DECAY ──── DEATH ──── RESURRECTION
   │           │           │          │            │
CreateCell  Turns,CapTP  Refs drop  Eviction    Owner proves
NoteCreate  Storage use  No turns   Tombstone   Re-hosts cell
            IVC grows    Rent due   Sovereignty
```

---

## Phase 1: BIRTH

### Hosted Cell Creation

```rust
// turn/src/executor.rs, line ~5028
// CreateCell effect allocates a new cell in the federation ledger
pyana_cell::CellMode::Hosted => Cell::new_hosted(*owner_pubkey, *token_id),
pyana_cell::CellMode::Sovereign => Cell::new(*owner_pubkey, *token_id),
```

At birth, a hosted cell:
- Is inserted into the federation's `Ledger` (full state stored)
- Has `state.nonce = 0`, `state.balance = initial_balance`
- Costs `ComputronCosts::create_cell` (500 computrons default) to create
- Gets a `CellId = BLAKE3(public_key || token_id)` (globally unique, federation-independent)
- Has no CapTP exports yet (`ExportGcManager` has no entry for it)

### Note Creation (Shielded Value Birth)

A note commitment is appended to the federation's Poseidon2 note tree
(`store/src/poseidon2_note_tree.rs`). The commitment is a leaf in a 4-ary
Merkle tree. Once appended, it cannot be removed without breaking sibling proofs.

**Lifecycle implication**: Notes are born immortal (append-only tree), but their
*economic value* decays when the nullifier set grows. This tension is resolved
by epoch-based tree rotation (Phase 3: Decay).

---

## Phase 2: ACTIVE LIFE

During active life, a cell accumulates:
- **Turns**: each turn advances nonce, modifies state, costs computrons
- **CapTP references**: other federations hold imports of this cell
- **History**: the IVC hash chain grows (but proof size stays constant)
- **Storage**: state fields, c-list entries, delegation snapshots

### CapTP Reference Tracking

```rust
// captp/src/gc.rs, ExportGcManager::record_export (line 79)
// Called when a capability is introduced to a peer federation
pub fn record_export(&mut self, cell_id: CellId, to_federation: FederationId, current_height: u64)
```

Every external reference to this cell increments a per-federation refcount.
The `last_activity` field (line 31) tracks when each holder last interacted,
enabling staleness detection later.

### IVC Accumulation (History Compression During Life)

```rust
// circuit/src/ivc.rs, IvcBuilder (line 1294)
// Each fold step is accumulated without growing the proof
pub fn add_fold(&mut self, delta: FoldDelta) -> Result<(), &'static str>
```

A well-behaved cell periodically compresses its history via IVC. The
`SovereignHistory` struct (`cell/src/ledger.rs`, line 1392) tracks:
- `genesis_commitment`: the cell's birth state
- `current_commitment`: latest state
- `step_count`: total transitions
- `accumulated_hash`: Poseidon2 hash chain binding all history
- `ivc_proof`: optional compressed proof (produced offline by owner)

**Key property**: A cell that compresses its history is cheaper to migrate.
The IVC proof IS the history. No blocklace blocks need to travel with the cell.

### Storage Metering

```rust
// turn/src/executor.rs, ComputronCosts (line 75)
pub struct ComputronCosts {
    pub action_base: u64,     // 100 computrons per action
    pub effect_base: u64,     // 50 per effect
    pub create_cell: u64,     // 500 per new cell
    pub per_byte: u64,        // 1 per byte processed
    // ...
}
```

Every turn depletes the cell's balance. When balance reaches zero, the cell
cannot execute turns (no more economic activity). This is the first signal
of decay.

---

## Phase 3: DECAY

Decay is detected through multiple signals that converge to a unified scoring:

### Signal 1: CapTP Reference Drop (External Disinterest)

```rust
// captp/src/gc.rs, stale_exports (line 146)
pub fn stale_exports(&self, max_idle_blocks: u64, current_height: u64) -> Vec<CellId>
```

When `ExportGcManager::stale_exports()` returns a cell, ALL external holders
have been idle for longer than `max_idle_blocks`. This means nobody outside the
federation cares about this cell anymore.

When `process_drop()` returns `DropResult::CanRevoke` (line 134), the cell has
zero external references. Combined with internal inactivity, this makes the cell
a GC candidate.

### Signal 2: No Internal Activity (Turns Stopped)

For sovereign cells, the `SovereignRegistration` tracks `last_activity`:

```rust
// cell/src/ledger.rs, expire_sovereign_registrations (line 1196)
pub fn expire_sovereign_registrations(&mut self, current_height: u64) -> usize {
    self.sovereign_registrations
        .retain(|_, reg| current_height.saturating_sub(reg.last_activity) <= reg.ttl_blocks);
    ...
}
```

For hosted cells, the same principle applies: the ledger can track when a cell
last executed a turn. If `current_height - last_turn_height > decay_threshold`,
the cell is decaying.

### Signal 3: Balance Depletion (Cannot Pay Rent)

When a cell's balance hits zero, it cannot:
- Pay for new turns (computron cost > 0)
- Pay state rent (proposed `expires_at` field)
- Participate in the federation's economy

This is analogous to the `timeout_waves` mechanism for nodes, but for cells.

### Signal 4: Note Epoch Expiry (Tree Rotation)

**Unification insight**: epoch-based tree rotation IS migration.

When the federation starts a new note tree epoch:
1. A fresh Poseidon2 tree is initialized
2. Unspent notes in the old tree must "migrate" to the new tree
3. Migration proof: `non_membership(nullifier_set) + membership(old_tree) -> commit(new_tree)`
4. Notes that don't migrate within the grace period become "sovereign"
   (the holder retains the Merkle proof but the federation drops it)

This mirrors exactly how cell migration works:
- Old tree = source federation
- New tree = target federation
- Migration proof = `CellExportBundle` with IVC proof
- Grace period = `T_MIGRATION_TIMEOUT` from vat-migration-design.md

### Unified Decay Score

```
decay_score(cell) =
    w1 * (current_height - last_turn_height) / decay_epochs +
    w2 * (1 - external_ref_count / peak_ref_count) +
    w3 * (1 - balance / initial_balance) +
    w4 * (state_size_bytes / max_state_size)
```

When `decay_score >= 1.0`, the cell enters Phase 4.

---

## Phase 4: DEATH (GC as Graceful Migration)

**Current approach** (destructive): Cell is evicted, state is lost.

**Unified approach**: Death is a forced migration to sovereignty.

### Step 1: Propose Departure (Constitutional)

Extend the timeout mechanism already used for nodes:

```rust
// blocklace/src/constitution.rs, LeaveReason::Timeout (line 222)
// Currently applies to NODES. Extend to CELLS:
pub enum CellLeaveReason {
    /// Owner requested departure (voluntary sovereignty transition).
    Voluntary,
    /// Cell timed out: no turns for `timeout_epochs` consecutive epochs.
    Timeout { last_active_epoch: u64, detected_at_epoch: u64 },
    /// Cell cannot pay rent (balance depleted).
    RentDefault { balance: u64, required_rent: u64 },
    /// External refs dropped to zero + internal inactivity.
    Unreferenced { stale_since_height: u64 },
}
```

The federation proposes `CellDeparture` using the same voting mechanism
as `MembershipProposal::Leave`:

```rust
// From vat-migration-design.md, Section 9.3
MembershipProposal::CellDeparture {
    cells: Vec<CellId>,
    destination: FederationId,  // or: DestinationSovereign
}
```

### Step 2: Freeze + Export Bundle

The migration protocol from `vat-migration-design.md` Section 1.1 applies:

```
Phase 1: FREEZE
  - Mark cell as FROZEN (reject new turns)
  - Wait for pending turns to commit/abort

Phase 2: EXPORT
  - Build CellExportBundle (state + IVC proof + swiss entries)
  - If owner is online: deliver bundle to owner (sovereignty transition)
  - If owner is offline: encrypt bundle to owner's public key, store as tombstone
```

### Step 3: Tombstone (Privacy-Preserving Death)

**Can the federation GC a cell WITHOUT learning which cell it was?**

Yes, using stealth tombstones:

```rust
// Proposed structure
pub struct StealthTombstone {
    /// Encrypted CellExportBundle (only owner can decrypt).
    /// Uses the cell owner's X25519 view key from StealthMetaAddress.
    pub encrypted_bundle: Vec<u8>,
    /// Ephemeral DH key for decryption (same pattern as stealth.rs line 64).
    pub ephemeral_pubkey: [u8; 32],
    /// TTL for the tombstone itself (after which relay drops it).
    pub ttl_blocks: u64,
    /// Forwarding address: messages to the dead cell are queued here.
    /// Uses store-and-forward (captp/src/store_forward.rs).
    pub forward_queue: Option<FederationId>,
}
```

The federation replaces the cell's ledger entry with a tombstone. Externally,
it's indistinguishable from any other departed cell. The stealth address
machinery (`cell/src/stealth.rs`) ensures the tombstone's content is unlinkable
to the cell's public identity.

### Step 4: Store-and-Forward for Absent Cells

```rust
// captp/src/store_forward.rs, QueuedMessage (line 46)
pub struct QueuedMessage {
    pub destination: FederationId,
    pub encrypted_payload: Vec<u8>,
    pub sender_ephemeral_pk: [u8; 32],
    pub causal_sequence: u64,
    pub queued_at: u64,
    pub ttl_blocks: u64,
    pub priority: MessagePriority,
}
```

When a message arrives for a dead/departed cell:
1. If tombstone has `forward_queue`: encrypt and queue (store-and-forward)
2. If no forwarding: respond with `RedirectNotice` (from vat-migration-design.md)
3. If neither: respond with "gone permanently" (CapTP abort)

Queue priority: GC notifications are `MessagePriority::Low` (line 36), so they're
evicted first under storage pressure. Payments are `High`, ensuring critical
messages survive.

### Step 5: Federation State Freed

After the tombstone is created:
- Cell removed from `Ledger.cells` HashMap
- Sovereign registration removed from `sovereign_registrations`
- ExportGcManager entry cleaned via `gc_sweep()` (line 162)
- Swiss table entries removed (cell is gone, sturdy refs won't work)
- Blocklace history below checkpoint: already prunable via `prune_before()` (`store/src/checkpoint.rs`, line 124)

**Net effect on federation**: One cell's worth of state is replaced by a
tombstone (encrypted bundle + ephemeral key + TTL). The tombstone has its own
TTL. After the tombstone TTL expires, the federation's state cost drops to ZERO.

---

## Phase 5: RESURRECTION

The owner returns and wants their cell back. Three paths:

### Path A: Self-Sovereignty (Zero Federation Cost)

Owner decrypts the tombstone bundle using their view key, runs the cell on their
own device. The cell operates in `CellMode::Sovereign` with no federation hosting.

```rust
// cell/src/cell.rs, CellMode::Sovereign (line 16)
// Federation stores only a 32-byte state commitment.
// The agent must provide cell state in each turn.
```

If the owner later needs federation services (ordering, nullifier checks,
proving to strangers), they re-register:

```rust
// cell/src/ledger.rs, SovereignRegistration (line 228)
pub struct SovereignRegistration {
    pub commitment: [u8; 32],
    pub registered_at: u64,
    pub ttl_blocks: u64,
    pub last_activity: u64,
    pub verification_key_hash: Option<[u8; 32]>,
}
```

### Path B: Re-Host at Original Federation

Owner submits a `MembershipProposal::CellArrival` (from vat-migration-design.md):
- Provides the `CellExportBundle` (decrypted from tombstone)
- IVC proof validates the cell's full history
- Federation votes to accept (threshold approval)
- Cell re-enters the ledger as hosted

### Path C: Migrate to a Different Federation

The dead cell's bundle is a valid `CellExportBundle`. The owner can present it
to ANY federation as a migration request. The target validates:
1. IVC proof (history is valid from genesis)
2. Owner signature (authorization)
3. No double-hosting (source federation's tombstone serves as exit proof)

This is exactly the Phase 3 (VALIDATE) from vat-migration-design.md Section 1.1.

---

## IVC Compression as In-Place GC

Instead of migrating state to reduce cost, compress history in-place:

```rust
// circuit/src/ivc.rs, prove_ivc (line 786)
pub fn prove_ivc(initial_root: BabyBear, deltas: Vec<FoldDelta>) -> Option<IvcProof>
```

The IVC proof IS the history. Properties:
- **Constant size**: `IVC_CONSTANT_PROOF_SIZE = 131_072` bytes (128 KiB) regardless of step count
- **Logarithmic cost**: `ivc_proof_size(step_count)` scales as O(log N) via FRI
- **Self-validating**: `verify_ivc()` checks everything without access to intermediate states

**Deep GC via IVC**:
1. Cell has 10,000 turns of history in the blocklace
2. Owner produces IVC proof covering all 10,000 transitions
3. Attach proof to `SovereignHistory.ivc_proof` (line 1406)
4. Federation prunes all blocklace blocks below the IVC checkpoint
5. Result: 10,000 blocks (~5 MB) replaced by one proof (~128 KiB)

The `prune_before()` method (`store/src/checkpoint.rs`, line 124) already
implements this for the general case. IVC-aware pruning extends it:

```
If cell has valid IVC proof covering [genesis, height_H]:
    prune all cell-specific blocks below H
    retain only: current state + IVC proof + checkpoint reference
```

### Validated IVC for Maximum Trust Reduction

```rust
// circuit/src/ivc.rs, prove_validated_ivc (line 1564)
// Chain STARK + per-step Merkle membership STARKs
pub fn prove_validated_ivc(
    initial_root: BabyBear,
    fold_witnesses: &[FoldStepWitness],
) -> Result<ValidatedIvcProof, String>
```

For the strongest guarantee (no trust in the cell owner), the validated IVC
path produces a `ValidatedIvcProof` that includes:
- Hash-chain STARK (proves ordering, from `StateTransitionAir`)
- Per-step Merkle membership proofs (proves each fold was valid)
- Cross-checked roots (chain proof roots match membership proof roots)

A cell with a validated IVC proof can be resurrected at ANY federation with
zero trust in the prior host.

---

## Epoch-Based Tree Rotation as Migration

The note tree grows forever (append-only Merkle). Epoch rotation makes it finite:

```
Epoch 0:  [note_0, note_1, ..., note_K]     <- frozen after epoch boundary
Epoch 1:  [migrated_notes, new_notes, ...]   <- current active tree
```

### Migration Protocol for Notes

A note "migrates" from epoch N to epoch N+1 via:

1. **Non-spending proof**: Prove `nullifier(note) NOT IN nullifier_set`
   (the note hasn't been spent)
2. **Membership proof**: Prove `commitment(note) IN tree_epoch_N`
   (the note existed in the old tree)
3. **Re-commitment**: Insert `commitment(note)` into `tree_epoch_N+1`
   (the note now lives in the new tree)

This is structurally identical to cell migration:
- Source = old epoch tree
- Target = new epoch tree
- Export proof = non-spending + membership
- Import = re-commitment

### Non-Migrated Notes Become Sovereign

If the holder doesn't migrate their note within the grace period:
- The federation drops the old tree from active storage (archival only)
- The holder retains their Merkle proof locally (they can still prove ownership)
- If the holder later wants to spend: they must provide the old-tree proof
  alongside the spend, and the federation verifies against the archived root

This is exactly the sovereignty escape hatch: the note's "state" (the Merkle
proof) lives on the owner's device, not on the federation.

---

## Federation-Level GC Sweep (Composing All Signals)

A periodic sweep composes all decay signals:

```rust
/// Proposed: federation-level GC sweep
pub fn gc_sweep(
    ledger: &Ledger,
    export_gc: &ExportGcManager,
    current_height: u64,
    config: &GcConfig,
) -> Vec<GcAction> {
    let mut actions = Vec::new();

    // 1. Expire sovereign registrations (already implemented)
    // cell/src/ledger.rs:1196
    let expired_sovereign = ledger.expire_sovereign_registrations(current_height);

    // 2. Find stale exports (no external interest)
    // captp/src/gc.rs:146
    let stale = export_gc.stale_exports(config.max_idle_blocks, current_height);

    // 3. Find balance-depleted cells (cannot pay rent)
    let bankrupt: Vec<CellId> = ledger.cells()
        .filter(|c| c.state.balance == 0)
        .filter(|c| current_height - c.last_turn_height > config.grace_period)
        .map(|c| c.id)
        .collect();

    // 4. Intersect: cells that are stale AND bankrupt AND inactive
    for cell_id in bankrupt {
        if stale.contains(&cell_id) {
            actions.push(GcAction::ProposeDeparture {
                cell_id,
                reason: CellLeaveReason::Unreferenced {
                    stale_since_height: current_height,
                },
            });
        }
    }

    // 5. Cells with IVC proofs can be deep-pruned (history compression)
    for cell_id in ledger.cells_with_ivc_proofs() {
        actions.push(GcAction::PruneHistory {
            cell_id,
            prune_below: current_height - config.ivc_retention_blocks,
        });
    }

    actions
}
```

### GC Actions (Composable)

```rust
pub enum GcAction {
    /// Propose the cell for departure (constitutional vote needed).
    ProposeDeparture { cell_id: CellId, reason: CellLeaveReason },
    /// Prune history below a checkpoint (non-destructive to current state).
    PruneHistory { cell_id: CellId, prune_below: u64 },
    /// Force sovereignty transition (cell becomes sovereign, federation drops state).
    ForceSovereignty { cell_id: CellId },
    /// Create tombstone and queue store-and-forward.
    CreateTombstone { cell_id: CellId, ttl_blocks: u64 },
    /// Compact: compress turns into IVC proof and prune blocks.
    CompactToIvc { cell_id: CellId },
}
```

---

## Privacy-Preserving GC

### Can the federation GC a cell WITHOUT knowing which cell?

**Yes**, using the ring membership proof from `circuit/src/presentation.rs`:

1. The GC proposer proves "there exists a cell with decay_score >= 1.0"
   without revealing which cell, using a blinded Merkle membership proof
2. The proposal is a ZK proof: `EXISTS cell IN ledger WHERE decay_score(cell) >= 1.0`
3. After threshold votes: the cell is replaced with a stealth tombstone
4. The replacement is done by the cell's OWN last known key (self-eviction)

**Limitation**: This only works if the cell owner cooperates (signs the eviction).
For forced eviction of non-cooperative cells, the federation necessarily learns
the cell's identity (to freeze it and build the export bundle).

**Practical middle ground**: Anonymous eviction for sovereign cells (the
federation only knows a commitment, not the cell's content), identified eviction
for hosted cells (the federation already has full state).

---

## Integration Points with Existing Code

| Mechanism | Code Path | Role in Lifecycle |
|-----------|-----------|-------------------|
| Cell creation | `turn/src/executor.rs:5028` | Birth |
| Computron metering | `turn/src/executor.rs:75` (ComputronCosts) | Active life cost |
| CapTP ref tracking | `captp/src/gc.rs:79` (record_export) | Active life visibility |
| Stale export detection | `captp/src/gc.rs:146` (stale_exports) | Decay signal |
| CapTP ref drop | `captp/src/gc.rs:111` (process_drop) | Decay signal |
| Sovereign TTL expiry | `cell/src/ledger.rs:1196` (expire_sovereign_registrations) | Death trigger |
| Constitutional timeout | `blocklace/src/constitution.rs:222` (LeaveReason::Timeout) | Death model |
| Store-and-forward | `captp/src/store_forward.rs:46` (QueuedMessage) | Post-death messages |
| IVC compression | `circuit/src/ivc.rs:786` (prove_ivc) | In-place GC |
| IVC validation | `circuit/src/ivc.rs:1564` (prove_validated_ivc) | Resurrection trust |
| Blocklace pruning | `store/src/checkpoint.rs:124` (prune_before) | History GC |
| Stealth addresses | `cell/src/stealth.rs:41` (StealthMetaAddress) | Private tombstones |
| Sovereign history | `cell/src/ledger.rs:1392` (SovereignHistory) | Compressed cell state |
| Migration export | `plans/vat-migration-design.md` Section 1.1 | Death protocol |

---

## Economics: Why This Converges

The unified lifecycle creates natural economic pressure:

1. **Active cells pay rent** (computrons per turn, scaling with state size)
2. **Inactive cells stop paying** (balance depletes, no turns executed)
3. **Depleted cells are proposed for departure** (GC sweep detects them)
4. **Departure = sovereignty** (cheapest GC: owner takes their own state)
5. **Sovereignty = zero federation cost** (32-byte commitment or nothing)
6. **Owners who care will compress** (IVC proof = resurrection ticket)
7. **Owners who don't care lose nothing** (their state was never theirs to keep on the federation)

The federation naturally sheds state over time. Cells that generate value stay
(they can pay rent). Cells that don't generate value leave (they become sovereign
or disappear). This is the "grassroots" property: the network doesn't grow
proportionally to its user count because most users carry their own state.

---

## Implementation Priority

### Immediate (Devnet)

1. **Add `last_turn_height` to hosted cells** — enables decay detection
2. **Wire `expire_sovereign_registrations()` into the epoch tick** — already implemented, needs scheduling
3. **Compose `stale_exports()` + balance check into a sweep task** — simple periodic job

### Soon (Testnet)

4. **CellDeparture proposal variant** — extend `MembershipProposal` (constitution.rs)
5. **Tombstone struct + encrypted export** — stealth.rs pattern applied to GC
6. **IVC-aware pruning** — extend `prune_before()` to check for attached IVC proofs

### Research (Mainnet)

7. **Note tree epoch rotation** — the "note migration" protocol above
8. **Privacy-preserving GC** — ring membership proofs for anonymous eviction
9. **Decay scoring function** — tunable weights, economic equilibrium analysis
10. **Cold storage tier** — erasure-coded archival for tombstone bundles

---

## Nullifier Immortality (The One Unsolved Problem)

Nullifiers genuinely grow forever. The lifecycle doesn't help here because
removing a nullifier enables double-spending. The mitigation strategies from
`honey-i-need-to-shrink-the-kids.md` still apply:

- **Algebraic accumulator**: `AccumulatorNonRevocationAir` already exists, extend to nullifiers
- **Epoch-based nullifier sets**: controversial (old notes become double-spendable)
- **Accept it**: 32 bytes per spent note; 1 million notes = 32 MB (manageable for years)

The lifecycle's contribution: by migrating cells to sovereignty, fewer cells are
hosted, which means fewer turns are executed on-federation, which means the
nullifier growth rate is bounded by the ACTIVE federation population rather than
the cumulative historical population. Sovereignty migration moves the nullifier
burden to the holder's local device.
